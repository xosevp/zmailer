/*
 *	Copyright 1988 by Rayan S. Zachariassen, all rights reserved.
 *	This will be free software, but only when it is finished.
 */
/*
 *	Lots of modifications (new guts, more or less..) by
 *	Matti Aarnio <mea@nic.funet.fi>  (copyright) 1992-2007
 */

/*
 * ZMailer transport scheduler.
 */

#include <stdio.h>
#include <sfio.h>

#include <sys/param.h>
#include "hostenv.h"
#include <ctype.h>
#include <errno.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "mail.h"
#include <string.h>
#include "ta.h"
#include "sysexits.h"
#include "libc.h"

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#ifdef HAVE_DIRENT_H
# include <dirent.h>
#else /* not HAVE_DIRENT_H */
# define dirent direct
# ifdef HAVE_SYS_NDIR_H
#  include <sys/ndir.h>
# endif /* HAVE_SYS_NDIR_H */
# ifdef HAVE_SYS_DIR_H
#  include <sys/dir.h>
# endif /* HAVE_SYS_DIR_H */
# ifdef HAVE_NDIR_H
#  include <ndir.h>
# endif /* HAVE_NDIR_H */
#endif /* HAVE_DIRENT_H */

#include "zmsignal.h"
#ifdef HAVE_MMAP
#include <sys/mman.h>
#endif

#include "scheduler.h"
#include "prototypes.h"
#include "zsyslog.h"
#include "libz.h"
#include <grp.h>

extern int optind;
extern char *optarg;

#ifndef	MAXNAMLEN /* POSIX.1 ... */
#define MAXNAMLEN NAME_MAX
#endif

#ifndef	_IOLBF
# define _IOLBF 0200
#endif	/* !_IOLBF */

#ifdef	HONEYBUM/* not really SVID, just this stupid honeywell compiler */
# define MAX_ENTRIES 3000
#else	/* sane pcc */
# define MAX_ENTRIES 10000
#endif	/* honeywell pcc */

struct sptree *spt_mesh[SIZE_L];

#define TRANSPORTMAXNOFILES 32 /* Number of files a transporter may
				  need open -- or any of its children.. */
int	transportmaxnofiles = TRANSPORTMAXNOFILES; /* Default value */
const char * progname;
extern const char * postoffice;
const char * rendezvous;
const char * pidfile = PID_SCHEDULER;
const char * mailshare;
const char * logfn;
const char * statusfn;
Sfio_t     * statuslog = NULL;
int	slow_shutdown = 0;
extern int readsockcnt; /* from transport.c: mux() */
 
static int mustexit = 0;
static int gotalarm = 0;
static int dumpq    = 0;
static int canexit  = 0;
static int rereadcf = 0;
static int dlyverbose = 0;
time_t	sched_starttime;
int	do_syslog = 0;
int	verbose = 0;
int	querysocket = -1;	/* fd of TCP socket to listen for queries */
int	querysocket6 = -1;	/* fd of TCP socket to listen for queries */
int	msgwriteasync = 0;
int	D_alloc = 0;
int	hungry_childs = 0;
int	global_wrkcnt = 0;
int	mailq_Q_mode = 0;
int	syncstart = 0;		/* while set, the thread subsystem shall start
				   no childs! */
int	freeze = 0;		/* For debugging, complete disable of child
				   running.. */
int	hashlevels = 0;		/* How many levels of hashes are supported
				   at the transport directory ?  (To speed
				   up the directory processing, file opens,
				   etc.. ) */
char * procselect = NULL;	/* Non-null defines  channel/host specifier
				   that is ALLOWED TO RUN, specifying this
				   (by means of '-P chan/host' -option) will
				   prevent running anything else, and also
				   prevent running error processing, or
				   job-specifier deletions. */
char *  procselhost = NULL;	/* Just spliced out 'host'-part of the above */
extern int forkrate_limit;	/* How many forks per second ? */
int	mailqmode = 1;		/* ZMailer v1.0 mode on mailq */
char *  mailqsock;
char *  notifysock;
int     QSpoolFd = -1;
int     TSpoolFd = -1;

int    interim_report_interval = 5*60; /* 5 minutes */

static int vtxprep_skip;
static int vtxprep_skip_any;
static int vtxprep_skip_lock;
static time_t next_dirscan;
static time_t next_idlecleanup;
static time_t next_interim_report_time;
static time_t next_expiry2_scan;
static struct sptree *dirscan_mesh;

static int newents_limit = 40000;
static int newents_timelimit = 5;

extern int default_full_content; /* on conf.c */

#include "memtypes.h"
extern memtypes stickymem;

static struct ctlfile *schedule __((int fd, const char *file, long ino, const int));
static struct ctlfile *vtxprep __((struct ctlfile *, const char *, const int));
static int  vtxmatch __((struct vertex *, struct config_entry *));
static void link_in __((int flag, struct vertex *vp, const char *s));
static int  lockverify __((struct ctlfile *, const char *, const int));
static int  globmatch   __((const char *, const char*));
static void vtxdo   __((struct vertex *, struct config_entry *, const char *));

extern void  cfp_mksubdirs __((const char *, const char*));

static RETSIGTYPE sig_exit   __((int sig));
static RETSIGTYPE sig_quit   __((int sig));
static RETSIGTYPE sig_alarm  __((int sig));
static RETSIGTYPE sig_iot    __((int sig));
static RETSIGTYPE sig_readcf __((int sig));

extern char *strerror __((int err));

extern time_t mytime          __((time_t *));
static void   init_timeserver __((void));

#ifdef HAVE_SELECT /* Well, not exactly kosher assumption.. */
/* extern int gettimeofday __((struct timeval *,)); */
#else
extern time_t time __((time_t *));
#endif

struct itimerval profiler_itimer_at_start;

static int loginitsched __((int));
static int loginitsched(sig)
int sig;
{
	int flags;

	if (logfn != NULL) {
	  sfsync(sfstdout);
	  sfseek(sfstdout, 0, 0);
	  sfsync(sfstderr);
	  sfseek(sfstderr, 0, 0);
	  if (sfopen(sfstdout, logfn, "a") != sfstdout
	      || dup2(sffileno(sfstdout), sffileno(sfstderr)) < 0) {	/* sigh */
	    /* XX: stderr might be closed at this point... */
	    sfprintf(sfstderr, "%s: cannot open log: %s, errno=%d\n", progname, logfn, errno);
	    return -1;
	  }
#if	defined(F_SETFL) && defined(O_APPEND)
	  flags = fcntl(sffileno(sfstdout), F_GETFL, 0);
	  flags |= O_APPEND;
	  fcntl(sffileno(sfstdout), F_SETFL, flags);
#endif	/* F_SETFL */
#if defined(F_SETFD)
	  fcntl(sffileno(sfstdout), F_SETFD, 1); /* close-on-exec */
#endif
	  sfset(sfstdout, SF_LINE, 1);
	  sfset(sfstderr, SF_LINE, 1);
	}
	if (statusfn != NULL && statuslog != NULL) {
	  sfclose(statuslog);
	  if (sfopen(NULL, statusfn, "a") != statuslog) {
	    sfprintf(sfstderr,"%s: cannot open statuslog: %s, errno=%d\n", progname, statusfn, errno);
	    return -1;
	  }
	  sfset(statuslog, SF_WHOLE, 1);
#if defined(F_SETFD)
	  fcntl(sffileno(statuslog), F_SETFD, 1); /* close-on-exec */
#endif
	}
	SIGNAL_HANDLE(SIGHUP, (RETSIGTYPE(*)__((int))) loginitsched);
	return 0;
}

/*
 *  A self-timed log re-init caller to make sure, that
 *  no log file is kept open for more than 30 seconds
 *  in one go.  This allows (within 30 seconds) the files
 *  to be rotates at first to new names, then after that
 *  30 second delay, to be further processed - e.g. compressed.
 *
 */

void timed_log_reinit()
{
  static time_t next_log_reinit;

  mytime(&now);

  if (next_log_reinit < now) {
    struct stat stbuf;

    next_log_reinit = now + 25;
    loginitsched(SIGHUP);

    if (logfn != NULL &&
	lstat(logfn,&stbuf) == 0 &&
	S_ISREG(stbuf.st_mode)) {

      long bavail, bused, iavail, iused;
      if (! fd_statfs(sffileno(sfstdout), &bavail, &bused, &iavail, &iused)) {
	MIBMtaEntry->sys.LogUsedSpace = bused;
	MIBMtaEntry->sys.LogFreeSpace = bavail;
	MIBMtaEntry->sys.LogUsedFiles = iused;
	MIBMtaEntry->sys.LogFreeFiles = iavail;
      }
    }
  }
}



struct dirstatname {
	struct stat st;
	long ino;
	time_t	not_before;
	char name[1]; /* Allocate enough size */
};
struct dirqueue {
	int	wrksum;
	int	sorted;
	int	wrkcount;
	int	wrkspace;
	int	wrkcount2; /* Back-pushed material a *2 -queue */
	int	wrkspace2;
	struct dirstatname **stats;
	struct dirstatname **stats2;
};

static int dirqueuescan __((const char *dir,struct dirqueue *dq, int subdirs));
int syncweb __((struct dirqueue *dq));

int global_maxkids = 1000;
time_t now;

Sfio_t * vfp_open(cfp)
	struct ctlfile *cfp;
{
	Sfio_t *vfp;
	int fd;

	if (!cfp->vfpfn) return NULL;

	/* Open the vfp *ONLY* if the logging file exists,
	   and can be written to.  If the file does not
	   exist, no logging shall happen! */

	SETEUID(cfp->uid);
	fd = open(cfp->vfpfn, O_WRONLY|O_APPEND, 0);
	SETEUID(0);
	if (fd < 0) return NULL; /* Can't open it! */
	vfp = sfnew(NULL, NULL, 0, fd, SF_WRITE|SF_APPENDWR|SF_LINE);
	if (!vfp) return NULL; /* Failure to open */

	sfseek(vfp, (Sfoff_t)0, SEEK_END);
	return vfp;
}


static void cfp_free __((struct ctlfile *cfp, struct spblk *spl));
static void cfp_free0 __((struct ctlfile *cfp));

static void cfp_free0(cfp)
	struct ctlfile *cfp;
{

	struct vertex *vp, *nvp;

	/* Delete from memory */

	if (cfp->vfpfn) {
	  Sfio_t *vfp = vfp_open(cfp);
	  if (vfp) {
	    sfprintf(vfp,
		     "ordered deletion of task file from scheduler memory (%s)\n",
		     cfp->mid);
	    sfclose(vfp);
	  }
	}

	/* Throw all way, if no vertices.. */
	if (!cfp->head) {
	  /* This should *not* be happening.. */
	  sfprintf(sfstderr,
		   "%s: SHOULD NOT HAPPEN: (except for ETRN files - and locked messages) cfp->head == NULL; spoolid: %s\n",
		   progname, cfp->spoolid);
	  unctlfile(cfp, 1);
	  return;
	}

	for (vp = cfp->head; vp != NULL; vp = nvp) {
	  /* Stash the next pointer, because the VP content
	     WILL become trashed at the end of the loop. */
	  nvp = vp->next[L_CTLFILE];

	  MIBMtaEntry->sc.StoredRecipientsSc   -= vp->ngroup;
	  if (vp->thread) vp->thread->rcpts -= vp->ngroup;
	  vp->ngroup = 0;
	  unvertex(vp,1,1); /* Don't unlink()! Just free()! */
	}
	/* CFP freeup happens at last vertex's unvertex() */
}

static void cfp_free(cfp, spl)
	struct ctlfile *cfp;
	struct spblk   *spl;
{
	/* Delete from the  spt_mesh[]  */

	if (spl == NULL && cfp->id)
	  spl = sp_lookup((u_long)(cfp->id), spt_mesh[L_CTLFILE]);
	if (spl != NULL)
	  sp_delete(spl, spt_mesh[L_CTLFILE]);

	/* And from the memory */

	cfp_free0(cfp);
}


static int ctl_free __((void *, struct spblk *spl));
static int ctl_free(p, spl)
	void *p;
	struct spblk *spl;
{
	cfp_free((struct ctlfile *)spl->data, NULL);
	return 0;
}


/*
 *  free_cfp_memory(cfp) -- release all of the memory associated with the
 *  control file -- some of it is conditionally allocated, or perhaps
 *  previously released..  (cfp->contents, for example)
 */
void free_cfp_memory(cfp)
	struct ctlfile *cfp;
{
	if (cfp->contents)	free(cfp->contents);
	if (cfp->vfpfn)		free(cfp->vfpfn);
	if (cfp->spoolid)	free(cfp->spoolid);
	if (cfp->mid)		free(cfp->mid);
	if (cfp->erroraddr)	free(cfp->erroraddr);
	if (cfp->logident)	free(cfp->logident);
	if (cfp->envid)		free(cfp->envid);

	/* memset(cfp, 0x55, sizeof(*cfp)); */

	free((char *)cfp);

	--global_wrkcnt;
	--MIBMtaEntry->sc.StoredMessagesSc;
}


struct dirqueue dirqb = { 0, };
struct dirqueue *dirq = &dirqb;

char *ArgvSave;
const char *EOArgvSave;

extern int main __((int, const char **));

static struct config_entry *cehead = NULL;


/* #define GLIBC_MALLOC_DEBUG__ */
#ifdef GLIBC_MALLOC_DEBUG__ /* memory allocation debugging with GLIBC */

#include <malloc.h> /* GLIBC malloc.h ! */

/* Global variables used to hold underlaying hook values.  */
static void *(*old_malloc_hook) (size_t, const void * );
static void *(*old_realloc_hook) (void *, size_t, const void *);
static void (*old_free_hook) (void*, const void *);
static void *(*old_memalign_hook) (size_t, size_t, const void *);

/* Prototypes for our hooks.  */
static void *my_malloc_hook  (size_t, const void*);
static void *my_realloc_hook (void *,size_t, const void*);
static void  my_free_hook    (void*, const void*);
static void *my_memalign_hook  (size_t, size_t, const void*);
     
static void *
my_malloc_hook (size_t size, const void *CALLER)
{
  void *result;
  /* Restore all old hooks */
  __malloc_hook = old_malloc_hook;
  __free_hook   = old_free_hook;
  /* Call recursively */
  result = malloc (size);
  /* Save underlaying hooks */
  old_malloc_hook = __malloc_hook;
  old_free_hook   = __free_hook;
  /* `printf' might call `malloc', so protect it too. */
  sfprintf(sfstderr,"# malloc (%u) returns %p @%p\n",
	   (unsigned int) size, result, CALLER);
  /* Restore our own hooks */
  __malloc_hook = my_malloc_hook;
  __free_hook = my_free_hook;
  return result;
}

static void *
my_realloc_hook (void *ptr, size_t size, const void *CALLER)
{
  void *result;
  /* Restore all old hooks */
  __realloc_hook = old_realloc_hook;
  __malloc_hook = old_malloc_hook;
  __free_hook = old_free_hook;
  /* Call recursively */
  result = realloc (ptr, size);
  /* Save underlaying hooks */
  old_realloc_hook = __realloc_hook;
  old_malloc_hook  = __malloc_hook;
  old_free_hook    = __free_hook;
  /* `printf' might call `malloc', so protect it too. */
  sfprintf(sfstderr,"# realloc (%p,%u) returns %p @%p\n", ptr, (unsigned int) size, result, CALLER);
  /* Restore our own hooks */
  __realloc_hook = my_realloc_hook;
  __malloc_hook  = my_malloc_hook;
  __free_hook    = my_free_hook;
  return result;
}

static void *
my_memalign_hook (size_t align, size_t size, const void *CALLER)
{
  void *result;
  /* Restore all old hooks */
  __memalign_hook = old_memalign_hook;
  __malloc_hook = old_malloc_hook;
  __free_hook = old_free_hook;
  /* Call recursively */
  result = memalign (align, size);
  /* Save underlaying hooks */
  old_memalign_hook = __memalign_hook;
  old_malloc_hook  = __malloc_hook;
  old_free_hook    = __free_hook;
  /* `printf' might call `malloc', so protect it too. */
  sfprintf(sfstderr,"# memalign (%u,%u) returns %p @%p\n",
	   (unsigned)align, (unsigned)size, result, CALLER);
  /* Restore our own hooks */
  __memalign_hook = my_memalign_hook;
  __malloc_hook  = my_malloc_hook;
  __free_hook    = my_free_hook;
  return result;
}
     
static void
my_free_hook (void *ptr, const void *CALLER)
{
  /* Restore all old hooks */
  __malloc_hook = old_malloc_hook;
  __free_hook = old_free_hook;
  /* Call recursively */
  free (ptr);
  /* Save underlaying hooks */
  old_malloc_hook = __malloc_hook;
  old_free_hook = __free_hook;
  /* `printf' might call `free', so protect it too. */
  sfprintf(sfstderr,"# freed pointer %p @%p\n", ptr, CALLER);
  /* Restore our own hooks */
  __malloc_hook = my_malloc_hook;
  __free_hook = my_free_hook;
}
#endif

int
main(argc, argv)
	int argc;
	const char *argv[];
{
	struct ctlfile *cfp;
	const char *config, *cp;
	int i, daemonflg, c, errflg, version, fd;
	long offout, offerr;

	const char *t, *syslogflg;

	getitimer(ITIMER_PROF, & profiler_itimer_at_start);


#ifdef GLIBC_MALLOC_DEBUG__ /* memory allocation debugging with GLIBC */
	old_malloc_hook = __malloc_hook;
	__malloc_hook = my_malloc_hook;
	old_memalign_hook = __memalign_hook;
	__memalign_hook = my_memalign_hook;
	old_realloc_hook = __realloc_hook;
	__realloc_hook = my_realloc_hook;
	old_free_hook = __free_hook;
	__free_hook = my_free_hook;
#endif

#ifdef HAVE_SETGROUPS
	/* We null supplementary groups list entirely */
	setgroups(0, NULL);
#endif

	freeze = 0;
	/* setlinebuf(stderr);  -- no need for this ? */

	ArgvSave   = (char *) argv[0];
	EOArgvSave = argv[argc-1] + strlen(argv[argc-1]) + 1;

	time(&sched_starttime);

	memset(&dirqb,0,sizeof(dirqb));
	dirscan_mesh = sp_init();

	if ((progname = strrchr(argv[0], '/')) == NULL)
		progname = argv[0];
	else
		++progname;

	stickymem = MEM_MALLOC;

	resources_maximize_nofiles();

	/* The theory is, that scheduler needs circa 30 fd's for its own uses,
	   and it will use all others on child-process communication fifos. */
	/* Of these, 20 are for MQ2 sockets */

	global_maxkids = resources_query_nofiles()-30;

	/* Probe how many FDs each TA needs! */

	{
	  int to[2], from[2];
	  pipes_create(to,from);

	  close(to[0]); close(to[1]);

	  if (to[0] != from[1]) {

	    /* Two pipes! */
	    close(from[0]); close(from[1]);

	    global_maxkids >>= 1; /* Half the MAXKIDS count */

	  } /* else
	       Socketpair or equivalent bidirectional one!
	       Only one FD per child is used!               */
	}

	postoffice = rendezvous = logfn = statusfn = config = NULL;
	daemonflg = 1;
	dlyverbose = 0;
	syncstart = 0;
	verbose = errflg = version = 0;
	for (;;) {
		c = getopt(argc, (char*const*)argv,
			   "divE:f:Fl:HL:M:nN:p:P:q:QR:SVWZ:");
		if (c == EOF)
		  break;
		switch (c) {
		case 'f':	/* override default config file */
			config = optarg;
			break;
		case 'E':
		        sscanf(optarg, "%d,%d", &newents_limit, &newents_timelimit);

			if (newents_limit < 10)      newents_limit = 10;
			if (newents_timelimit < 2)   newents_timelimit = 2;
			if (newents_timelimit > 15)  newents_timelimit = 15;
			break;
		case 'F':
			freeze = 1;
			break;
		case 'l':
			statusfn = optarg;
			statuslog = sfopen(NULL, statusfn, "a");
			if (!statuslog) {
			  perror("Can't open statistics log file (-l)");
			  exit(1);
			}
			sfset(statuslog, SF_LINE, 1);
#if defined(F_SETFD)
			fcntl(sffileno(statuslog), F_SETFD, 1);
			/* close-on-exec */
#endif
			break;
		case 'H':
			if (hashlevels < 2)
				++hashlevels;
			break;
		case 'L':	/* override default log file */
			logfn = optarg;
			break;
		case 'M':
			mailqmode = atoi(optarg);
			if (mailqmode < 1 || mailqmode > 2) {
			  sfprintf(sfstderr,"scheduler: -M parameter is either 1, or 2\n");
			  exit(EX_USAGE);
			}
			break;
		case 'n':
			default_full_content = !default_full_content;
			break;
		case 'N':
			if ((transportmaxnofiles = atoi(optarg)) < 10)
				transportmaxnofiles = TRANSPORTMAXNOFILES;
			break;
		case 'p':
			procselect  = optarg;
			procselhost = strchr(procselect,'/');
			if (procselhost)
			  *procselhost++ = 0;
			else {
			  sfprintf(sfstderr,"scheduler: -p parameter is of form: channel/host\n");
			  exit(64);
			}
			break;
		case 'P':	/* override default postoffice */
			postoffice = optarg;
			break;
		case 'Q':
			mailq_Q_mode = 1;
			break;
		case 'q':	/* override default mail queue rendezvous */
			rendezvous = optarg;
			break;
		case 'R':	/* How many new childs per second to be spawned ? */
			forkrate_limit = atoi(optarg);
			if (forkrate_limit < 1)
			  forkrate_limit = 1;
			break;
		case 'v':	/* be verbose and synchronous */
			++verbose;
			daemonflg = 0;
			break;
		case 'W':
			dlyverbose = verbose;
			verbose = 0;
			break;
		case 'd':	/* daemon again */
			daemonflg = 1;
			break;
		case 'i':	/* interactive */
			daemonflg = 0;
			break;
		case 'V':
			version = 1;
			daemonflg = 0;
			break;
		case 'S':
			syncstart = 1;
			break;
		case 'Z':
			if (readzenv(optarg) == 0)
			  ++errflg;
			break;
		case '?':
		default:
			errflg++;
			break;
		}
	}

	if (errflg) {
	  sfprintf(sfstderr,
		   "Usage: %s [-dHisvV -M (1|2) -f configfile -L logfile -P postoffice -Q rendezvous -Z zenvfile]\n",
		   progname);
	  exit(128+errflg);
	}

	syslogflg = getzenv("SYSLOGFLG");
	if (syslogflg == NULL)
	  syslogflg = "";
	t = syslogflg;
	for ( ; *t ; ++t ) {
	  if (*t == 'c' || *t == 'C')
	    break;
	}
	do_syslog = (*t != '\0');


	cp = getzenv("SCHEDULERDIRHASH");
	if (cp){
	  if ((cp[0] == '1' || cp[0] == '2') &&
	      cp[1] == 0)
	    hashlevels = cp[0] - '0';
	}

	mailshare = getzenv("MAILSHARE");
	if (mailshare == NULL)
	  mailshare = MAILSHARE;
	cp = getzenv("LOGDIR");
	if (cp != NULL)
	  qlogdir = cp;
	if (daemonflg && logfn == NULL) {
	  logfn = emalloc(2 + (u_int)(strlen(qlogdir) + strlen(progname)));
	  sprintf((char*)logfn, "%s/%s", qlogdir, progname);
	}


	/* If we are a daemon, or doing verbose foobar, attach the SHM MIB now */
	if (daemonflg || verbose) {

	  int r = Z_SHM_MIB_Attach (1);

	  if (r < 0) {
	    /* Error processing -- magic set of constants: */
	    switch (r) {
	    case -1:
	      /* fprintf(stderr, "No ZENV variable: SNMPSHAREDFILE\n"); */
	      break;
	    case -2:
	      perror("Failed to open for exclusively creating of the SHMSHAREDFILE");
	      break;
	    case -3:
	      perror("Failure during creation fill of SGMSHAREDFILE");
	      break;
	    case -4:
	      perror("Failed to open the SHMSHAREDFILE at all");
	      break;
	    case -5:
	      perror("The SHMSHAREDFILE isn't of proper size! ");
	      break;
	    case -6:
	      perror("Failed to mmap() of SHMSHAREDFILE into memory");
	      break;
	    case -7:
	      fprintf(stderr, "The SHMSHAREDFILE  has magic value mismatch!\n");
	      break;
	    default:
	      break;
	    }
	    /* return; NO giving up! */
	  }
	}


#ifdef USE_SIGREAPER
# ifdef SIGCLD
	SIGNAL_HANDLE(SIGCLD,  sig_chld);
# else
	SIGNAL_HANDLE(SIGCHLD, sig_chld);
# endif
#else
# ifdef SIGCLD
	SIGNAL_HANDLE(SIGCLD,SIG_IGN);		/* Auto-reap the kids.. */
# else
	SIGNAL_HANDLE(SIGCHLD,SIG_IGN);
# endif
#endif

#ifdef	SIGUSR1
	SIGNAL_HANDLE(SIGUSR1, sig_readcf);
#endif	/* SIGUSR1 */
	if (verbose || version) {
	  prversion("scheduler");
	  if (version)
	    exit(0);
	  sfputc(sfstderr, '\n');
	}
	offout = sftell(sfstdout);
	offerr = sftell(sfstderr);
	if (config == NULL) {
	  config = emalloc(3 + (u_int)(strlen(mailshare)
				       + strlen(progname)
				       + strlen(qcf_suffix)));
	  sprintf((char*)config, "%s/%s.%s", mailshare, progname, qcf_suffix);
	}
	cehead = readconfig(config);
	if (cehead == NULL) {
	  cp = emalloc(strlen(config)+50);
	  sprintf((char*)cp, "null control file, probably errors in it: %s", config);
	  die(1, cp);
	  /* NOTREACHED */
	}

	if (postoffice == NULL && (postoffice = getzenv("POSTOFFICE")) == NULL)
	  postoffice = POSTOFFICE;

	if (chdir(postoffice) < 0 || chdir(TRANSPORTDIR) < 0)
	  sfprintf(sfstderr, "%s: cannot chdir to %s/%s.\n",
		   progname, postoffice, TRANSPORTDIR);


	if (logfn != NULL) {
	  /* loginit is a signal handler, so can't pass log */
	  if (loginitsched(SIGHUP) < 0) /* do setlinebuf() there */
	    die(1, "log initialization failure");
	  /* close and reopen log files */
	  SIGNAL_HANDLE(SIGHUP, (RETSIGTYPE(*)__((int))) loginitsched);
	} else {
	  SIGNAL_IGNORE(SIGHUP); /* no surprises please */
	  sfset(sfstdout, SF_LINE, 1);
	}


	if (rendezvous == NULL && (rendezvous = getzenv("RENDEZVOUS")) == NULL)
	  rendezvous = qoutputfile;
	if (daemonflg) {
	  /* X: check if another daemon is running already */
	  if (!verbose
	      && (offout < sftell(sfstdout) || offerr < sftell(sfstderr))) {
	    sfprintf(sfstderr, "%ld %ld %ld %ld\n", offout, sftell(sfstdout),
		     offerr, sftell(sfstderr));
	    sfprintf(sfstderr, "%s: daemon not started.\n", progname);
	    die(1, "too many scheduler daemons");
	    /* NOTREACHED */
	  }
	  detach();		/* leave worldy matters behind */

	  setitimer(ITIMER_PROF, &  profiler_itimer_at_start, NULL);

	  close(0);
	  open("/dev/null",O_RDONLY,0); /* This is good for fd0 reading.. */


	  time(&now);
	  sfprintf(sfstdout, "%s: scheduler daemon (%s)\n\tpid %d started at %s\n",
		   progname, Version, (int)getpid(), (char *)rfc822date(&now));
	}


	/* call this to create the timeserver -- if possible */
	init_timeserver(); /* Will take around 3-4 secs.. */


	/* Now we are either interactive, or daemon, lets attach monitoring
	   memory block.. and fill it in.  */

	MIBMtaEntry->sys.SchedulerMasterPID        = getpid();
	MIBMtaEntry->sys.SchedulerMasterStartTime  = time(NULL);
	MIBMtaEntry->sys.SchedulerMasterStarts    += 1;

	/* Zero the gauges at our startup.. */
	MIBMtaEntry->sc.StoredMessagesSc		= 0;
	MIBMtaEntry->sc.StoredThreadsSc			= 0;
	MIBMtaEntry->sc.StoredVerticesSc		= 0;
	MIBMtaEntry->sc.StoredRecipientsSc		= 0;
	MIBMtaEntry->sc.StoredVolumeSc			= 0;
	MIBMtaEntry->sc.TransportAgentProcessesSc	= 0;
	MIBMtaEntry->sc.TransportAgentsActiveSc		= 0;
	MIBMtaEntry->sc.TransportAgentsIdleSc		= 0;

	/* Zero also these transport agent gauges at our startup.. */
	MIBMtaEntry->tasmtp.TaProcCountG		= 0;
	MIBMtaEntry->tasmcm.TaProcCountG		= 0;
	MIBMtaEntry->tambox.TaProcCountG		= 0;
	MIBMtaEntry->tahold.TaProcCountG		= 0;
	MIBMtaEntry->taerrm.TaProcCountG		= 0;
	MIBMtaEntry->taexpi.TaProcCountG		= 0;
	MIBMtaEntry->tarert.TaProcCountG		= 0;

	/* Actually we want this to act as daemon,
	   even when not in daemon mode.. */
	if (killprevious(SIGTERM, pidfile) != 0) {
	  sfprintf(sfstdout, "%s: Can't write my pid to a file ?? Out of diskspace ??\n",progname);
	  die(1,"Can't write scheduler pid to a file!?");
	  /* NOTREACHED */
	}

	for (i = 0; i < SIZE_L; ++i) {
	  spt_mesh[i] = sp_init();
	  spt_mesh[i]->symbols = sp_init();
	}
	zopenlog("scheduler", LOG_PID, LOG_MAIL);

	mustexit = gotalarm = dumpq = rereadcf = 0;
	canexit = 0;
	SIGNAL_IGNORE(SIGPIPE);
	SIGNAL_HANDLE(SIGALRM, sig_alarm);	/* process agenda */
	SIGNAL_HANDLE(SIGUSR2, sig_iot);	/* dump queue info */

	SIGNAL_HANDLE(SIGTERM, sig_exit);	/* split */
	SIGNAL_HANDLE(SIGQUIT, sig_quit);	/* Slow shutdown */

	if (optind < argc) {
	  /* process the specified control files only */
	  for (; optind < argc; ++optind) {
	    long ino = atol(argv[optind]);
	    if ((fd = eopen(argv[optind], O_RDWR, 0)) < 0)
	      continue;
	    /* the close(fd) is done in vtxprep */
	    cfp = schedule(fd, argv[optind], ino, 0);
	    if (cfp == NULL) {
	      if (verbose)
		sfprintf(sfstderr, "Nothing scheduled for %s!\n",
			 argv[optind]);
	    } else
	      eunlink(argv[optind], "sch-argv");
	  }
	  doagenda();
	  killpidfile(pidfile);
	  exit(0);
	}

	queryipcinit();

	dirqueuescan(".", dirq, 1);

	vtxprep_skip_lock = 0;
	syncweb(dirq);

	canexit = 1;
#ifdef	MALLOC_TRACE
	mal_leaktrace(1);
#endif	/* MALLOC_TRACE */

	/* If we do a sync-start, we are synchronous.. */

	if (syncstart) {
	  int startcount;
	  dirqueuescan(".", dirq, 1);
	  startcount = dirq->wrksum;
	  while (dirq->wrksum > 0 && !mustexit) {
	    if (syncweb(dirq) < 0)
	      break;
	    queryipccheck();
	  }
	  sfprintf(sfstderr,"Synchronous startup completed, messages: %d (%d skipped) recipients: %d\n",
		   global_wrkcnt, startcount - global_wrkcnt, thread_count_recipients());
	  sfprintf(sfstderr,"***********************************************************************\n");
	  syncstart = 0;
	}

	if (dlyverbose) verbose = dlyverbose;

	do {
	  time_t timeout;

	  mytime(&now);

	  canexit = 0;

	  /* SAH Hmm... next_dirscan is NOT reset unless we find < 150
	   * new files in dirqueuescan - meaning this will be true.
	   * So a 'busy' system will potentially be running dirqueuescan()
	   * EVERY pass thru the loop... This could be bad
	   */

	  if (now >= next_dirscan) {
	    /* Directory scan time for new jobs ..    */
	    /* Do it recursively every now and then,
	       so that if we forget some jobs, they will
	       become relearned soon enough.          */
	    int wrk;
	    i = dirqueuescan(".", dirq, (now >= next_idlecleanup));
	    mytime(&now);
	    wrk = dirq->wrksum;
	    wrk >>= 5; /* Divide by 32 -- just presume 32 msgs/sec.. */
	    if (wrk > 10) wrk = 10; /* But limit to 10... */
	    next_dirscan = now + sweepinterval + wrk; /* 10 .. 20 second
							 sweep interval */
	  }

	  if (now >= next_idlecleanup) {
	    idle_cleanup();

	    if (next_idlecleanup == 0)  next_idlecleanup = now;

	    /* At regular intervals... */
	    next_idlecleanup += idle_sweepinterval;
	  }

	  if (now >= next_expiry2_scan) {
	    if (next_expiry2_scan == 0)  next_expiry2_scan = now;
	    i = doexpiry2();
	    if (i == 0) 
	      /* At regular intervals... */
	      next_expiry2_scan += expiry2_sweepinterval;
	  }

	  if (now >= next_interim_report_time) {
	    if (next_interim_report_time == 0) next_interim_report_time = now;
	    /* At regular intervals... */
	    next_interim_report_time += interim_report_interval;
	    interim_report_run();
	  }

	  /* See when to timeout from mux() */
	  timeout = next_dirscan;

	  /* If we still have things in pre-scheduler queue... */
	  if (dirq->wrksum > 0 &&
	      dirq->wrkcount > 0 &&
	      dirq->stats[ dirq->wrkcount-1 ]->not_before <= now)
	    timeout = now;

	  /* Submit possible new jobs (unless frozen) */
	  if (!freeze && !syncstart && doagenda() != 0)
	    timeout = now;	/* we still have some jobs avail for start */

	  gotalarm = 0;
	  canexit = 1;

	  /* mux on the stdout of children */
	  for (;;) {
	    if (dumpq) {
	      qprint(-1);
	      dumpq = 0;
	    }
	    if (rereadcf) {
	      cehead = rereadconfig(cehead, config);
	      rereadcf = 0;
	    }
	    mytime(&now);

	    /* Submit one item from pre-scheduler-queue into the scheduler */
	    if (dirq->wrksum > 1 ) {
	      /* If more things in queue, submit them up to 200 pieces, or
		 until spent two seconds at it! */
	      time_t now0 = now + 2;
	      for (i=0; i < 200 && now < now0; ++i) {
		if (syncweb(dirq) < 0)
		  break; /* Out of queue! */
		mytime(&now);
	      }
	    }
	    if (dirq->wrksum > 0)
	      syncweb(dirq);

	    if (slow_shutdown) {
	      timeout = now+2;
	      shutdown_kids();  /* If there are any to shut down.. */
	    }
	    if (!(mux(timeout) == 0 && !gotalarm &&
		  dirq->wrksum == 0 && !mustexit && timeout > now))
	      break;
	    if (readsockcnt == 0 && slow_shutdown) {
	      /* No more childs to read, hop hop die away! */
	      mustexit = 1;
	      break;
	    }
	  }
	} while (!mustexit);

	/* Doing nicely we would kill the childs here, but we are not
	   such a nice people -- we just discard incore data, and crash out.. */

	sp_scan(ctl_free, NULL, NULL, spt_mesh[L_CTLFILE]);

#ifdef	MALLOC_TRACE
	mal_dumpleaktrace(stderr);
#endif	/* MALLOC_TRACE */

	killpidfile(pidfile);

	if (mustexit)
		die(0, "signal");
	return 0;
}

static RETSIGTYPE sig_exit(sig)
int sig;
{
	
	if (querysocket >= 0) {		/* give up mailq socket asap */
		close(querysocket);
		querysocket = -1;
	}
	if (querysocket6 >= 0) {		/* give up mailq socket asap */
		close(querysocket6);
		querysocket6 = -1;
	}
	if (canexit)
		die(0, "signal");
	mustexit = 1;
}

static RETSIGTYPE sig_quit(sig)
int sig;
{
	slow_shutdown = 1;
	freeze = 1;
}


#ifdef SIGUSR2
static RETSIGTYPE sig_iot(sig)
int sig;
{
	dumpq = 1;
	SIGNAL_HANDLE(SIGUSR2, sig_iot);
}
#endif

#ifdef SIGUSR1
static RETSIGTYPE sig_readcf(sig)
int sig;
{
	rereadcf = 1;
	SIGNAL_HANDLE(SIGUSR1, sig_readcf);
}
#endif

/*
 * Absorb any new files that showed up in our directory.
 */

int
dq_insert(DQ, ino, file, delay)
	void *DQ;
	long ino;
	const char *file;
	int delay;
{
	struct stat stbuf;
	struct dirstatname *dsn;
	struct dirqueue *dq = DQ;

	if (!ino) return 1; /* Well, actually it isn't, but we "makebelieve" */

	mytime(&now);

	if (dq == NULL)
	  dq = dirq;

	if (lstat(file,&stbuf) != 0 ||
	    !S_ISREG(stbuf.st_mode)) {
	  /* Not a regular file.. Let it be there for the manager
	     to wonder.. */
	  return -1;
	}

	/* 
	   if (DQ == NULL)
	   sfprintf(sfstderr,"dq_insert(NULL,ino=%ld, file='%s', delay=%d)\n",
	   ino,file,delay);
	 */

	/* Is it already in the database ? */
	if (sp_lookup((u_long)ino,dirscan_mesh) != NULL) {
	  sfprintf(sfstderr,"scheduler: tried to dq_insert(ino=%ld, file='%s') already in queue\n",ino, file);
	  return 1; /* It is! */
	}

	/* Now store the entry */
	dsn = (struct dirstatname*)emalloc(sizeof(*dsn)+strlen(file)+1);
	memcpy(&(dsn->st),&stbuf,sizeof(stbuf));
	dsn->ino = ino;
	dsn->not_before = now + delay;
	strcpy(dsn->name,file);

	sp_install(ino, (void *)dsn, 0, dirscan_mesh);

	/* Put the new entry into the normal queue, unless there
	   is stuff at the delayed queue, OR the delay is positive! */

	if (delay <= 0 && dq->wrkcount2 == 0) {
	  /* Into the normal queue */
	  if (dq->wrkspace <= dq->wrkcount) {
	    /* Increase the space */
	    dq->wrkspace = dq->wrkspace ? dq->wrkspace << 1 : 8;
	    /* malloc(size) = realloc(NULL,size) */
	    dq->stats = (struct dirstatname**)erealloc(dq->stats,
						       sizeof(void*) *
						       dq->wrkspace);
	  }
	  dq->stats[dq->wrkcount] = dsn;
	  dq->wrkcount += 1;
	  dq->wrksum   += 1;
	  dq->sorted    = 0;
	} else {
	  /* Into the DELAYED QUEUE */
	  if (dq->wrkspace2 <= dq->wrkcount2) {
	    /* Increase the space */
	    dq->wrkspace2 = dq->wrkspace2 ? dq->wrkspace2 << 1 : 8;
	    /* malloc(size) = realloc(NULL,size) */
	    dq->stats2 = (struct dirstatname**)erealloc(dq->stats2,
							sizeof(void*) *
							dq->wrkspace2);
	  }
	  dq->stats2[dq->wrkcount2] = dsn;
	  dq->wrkcount2 += 1;
	  dq->wrksum    += 1;
	}
	++MIBMtaEntry->sc.ReceivedMessagesSc;
	return 0;
}

int in_dirscanqueue(DQ,ino)
	void *DQ;
	long ino;
{
	struct dirqueue *dq = DQ;

	if (dq == NULL)
	  dq = dirq;

	/* Return 1, if can find the "ino" in the queue */

	if (dq->wrksum == 0 || dirscan_mesh == NULL) return 0;
	if (sp_lookup((u_long)ino,dirscan_mesh) != NULL) return 1;
	return 0;
}

static int dq_ctimecompare __((const void *, const void *));
static int dq_ctimecompare(b,a) /* we want oldest entry LAST */
const void *a; const void *b;
{
	const struct dirstatname **A = (const struct dirstatname **)a;
	const struct dirstatname **B = (const struct dirstatname **)b;
	int rc;

#if 0
	if ((*A)->not_before > now) return  1;
	if ((*B)->not_before > now) return -1;
#endif

	rc = ((*A)->st.st_ctime - (*B)->st.st_ctime);
	return rc;
}

static int dirqueuescan(dir, dq, subdirs)
	const char *dir;
	struct dirqueue *dq;
	int subdirs;
{
	DIR *dirp;
	struct dirent *dp;
	struct stat stbuf;
	char file[MAXNAMLEN+1];
	int newents = 0;
	static time_t timelimit;
	time_t then;

	mytime( &now );
	then = now;

	if (dir && dir[0] == '.' && dir[1] == 0) {
	  timelimit = now + newents_timelimit;
	}

#if 0
	static time_t modtime = 0;

	/* Any changes lately ? */
	if (estat(dir, &stbuf) < 0)
	  return -1;	/* Could not stat.. */
	if (stbuf.st_mtime == modtime)
	  return 0;	/* any changes lately ? */
	modtime = stbuf.st_mtime;
#endif

	if (verbose && dir[0] == '.') {
	  sfprintf(sfstdout, "dirqueuescan(dir='%s') ",dir);
	  sfsync(sfstdout);
	}

	/* Some changes lately, open the dir and read it */

	dirp = opendir(dir);
	if (!dirp) {
	  sfprintf(sfstderr,"A 'this can never fail' opendir('%s') failed!; errno=%d (%s)\n",dir,errno,strerror(errno));
	  return 0;
	}

	for (dp = readdir(dirp); dp != NULL; dp = readdir(dirp)) {
	  /* Scan filenames into memory */

	  /* Here we are presuming the time retrieval is essentially
	     _free_ in form of shared memory segment.. */
	  mytime( &now );
	  if (now >  then) {
	    then = now;
	    queryipccheck();
	  }

	  if (!syncstart && now > timelimit)
	    break; /* At most  newents_timelimit  seconds in this scanner... */

	  if (!syncstart && newents > newents_limit)
	    break; /* At most NNN per one go */

	  if (subdirs &&
	      dp->d_name[0] >= 'A' &&
	      dp->d_name[0] <= 'Z' &&
	      dp->d_name[1] ==  0 ) {
	    /* We do this recursively.. */
	    if (dir[0] == '.' && dir[1] == 0)
	      strcpy(file, dp->d_name);
	    else
	      sprintf(file, "%s/%s", dir, dp->d_name);

	    if (lstat(file,&stbuf) != 0 ||
		!S_ISDIR(stbuf.st_mode)) {
	      /* Not a directory.. Let it be there for the manager
		 to wonder.. */
	      continue;
	    }
	    /* Recurse into levels below.. */
	    newents += dirqueuescan(file, dq, subdirs);
	    continue;
	  } /* End of directories of names "A" .. "Z" */

	  if (dp->d_name[0] >= '0' &&
	      dp->d_name[0] <= '9') {
	    /* A file whose name STARTS with a number (digit) */

	    long ino = atol(dp->d_name);
	    if (in_dirscanqueue(dq,ino))
	      /* Already in pre-schedule-queue */
	      continue;

	    if (dir[0] == '.' && dir[1] == 0)
	      strcpy(file, dp->d_name);
	    else
	      sprintf(file, "%s/%s", dir, dp->d_name);

	    /* We may have this file in processing state...  */
	    {
	      struct spblk *spl;
	      spl = sp_lookup((u_long)ino, spt_mesh[L_CTLFILE]);
	      if (spl != NULL) {
		/* Already in processing, don't touch.. */
		/*printf("File: %s active (not previously locked)\n",file);*/
		++vtxprep_skip_any;
		continue;
	      }
	    }

	    if (dq_insert(dq, ino, file, -1))
	      continue;

	    ++newents;
	  } /* ... end of "filename starts with a [0-9]" */
	}

#ifdef	BUGGY_CLOSEDIR
	/*
	 * Major serious bug time here;  some closedir()'s
	 * free dirp before referring to dirp->dd_fd. GRRR.
	 * XX: remove this when bug is eradicated from System V's.
	 */
	close(dirp->dd_fd);
#endif
	closedir(dirp);

	if (verbose && dir[0] == '.')
	  sfprintf(sfstdout,"wrksum=%d new=%d\n",dq->wrksum,newents);

	return newents;
}

int syncweb(dq)
	struct dirqueue *dq;
{
	struct stat *stbuf;
	char *file;
	struct dirstatname *dqstats;
	struct spblk *spl;
	int wrkcnt = 0;
	int wrkidx = dq->wrkcount -1;
	long ino;

	/* Any work to do ? */
	if (dq->wrksum == 0)  return -1;

	/* Be responsive, check query channel */
	queryipccheck();

	if (dq->wrkcount == 0 && dq->wrkcount2 > 0) {
	  /* Ok, the primary queue is empty, move the delayed
	     queue into the primary one. */
	  if (dq->stats != NULL) free(dq->stats);
	  dq->stats = dq->stats2;
	  dq->stats2 = NULL;
	  dq->wrkcount  = dq->wrkcount2;
	  dq->wrkcount2 = 0;
	  dq->wrkspace  = dq->wrkspace2;
	  dq->wrkspace2 = 0;
	  wrkidx = dq->wrkcount - 1; /* SAH ReSync wrkidx                    */
	  dq->sorted = 0;
	}

	if (!dq->sorted && dq->wrkcount > 1) {
	  /* Sort the dq->stats[] per file ctime -- LATEST on slot 0.
	     (we drain this queue from the END) */
	  mytime(&now);
	  qsort((void*)dq->stats,
		dq->wrkcount,
		sizeof(void*),
		dq_ctimecompare );
	  dq->sorted = 1;
	}

	mytime(&now);

	for (; wrkidx >= 0; --wrkidx) {

	  /* Process only one -- from the tail -- but leave
	     'not_before' things behind... */
	  if (dq->stats[wrkidx]->not_before > now)
	    continue; /* WAIT! */

	  break;
	}

	/* If the queue had only "not before" items ... */
	if (wrkidx < 0) return -1;

	/* Ok some, decrement the count to change it to index */
	dq->wrkcount -= 1;
	dq->wrksum   -= 1;

	dqstats = dq->stats[wrkidx];
	file  =   dqstats->name;
	stbuf = &(dqstats->st);
	ino   =   dqstats->ino;

	if (dq->wrkcount > wrkidx) {
	  /* Skipped some ! Compact the array ! */
	  memcpy( &dq->stats[wrkidx], &dq->stats[wrkidx+1],
		  sizeof(dq->stats[0]) * (dq->wrkcount - wrkidx));
	}
	dq->stats[dq->wrkcount] = NULL;

	/* Now we have pointers */

	/* Deletion from the  dirscan_mesh  should ALWAYS succeed.. */
	spl = sp_lookup((u_long)ino, dirscan_mesh);
	if (spl != NULL)
	  sp_delete(spl,dirscan_mesh);

	/* Sometimes we may get files already in processing
	   into our pre-schedule queue */

	/* Already in processing ? */
	spl = sp_lookup((u_long)ino, spt_mesh[L_CTLFILE]);
	if (spl == NULL) {
	  /* Not yet in processing! */
	  int fd;

	  /* Can open ? */
	  if ((fd = eopen(file, O_RDWR, 0)) < 0) {
	    /* Don't unlink here, ... */
	    /* errno == EMFILE  --> out of FDs!  URGH! */
#if 0
	    if (getuid() == 0)
	      eunlink(file,"sch-syncweb");	/* hrmpf! */
#endif
	  } else {
	    /* Ok, schedule! */
	    if (schedule(fd, file, ino, 0) != NULL) {
	      /* Success, increment counters */
	      ++wrkcnt;
	    }
	  }
	}

	/* Free the pre-schedule queue entry */
	free(dqstats);

	return wrkcnt;
}


static int sync_cfps __((struct ctlfile *,struct ctlfile *,struct procinfo*));
static int sync_cfps(oldcfp, newcfp, proc)
     struct ctlfile *oldcfp, *newcfp;
     struct procinfo *proc;
{
	struct vertex *ovp,  *nvp;
	struct vertex *novp, *nnvp;
	int ovp_count = 0;

	/* Scan both files thru their   vp->next[L_CTLFILE]  vertex chains.
	   If oldcfp has things that newcfp does not have, remove those from
	   oldcfp chains.

	   Chains start at  *cfp->head  pointer.

	   Comparisons can be done in linear order with respective
	   vp->orig[L_CHANNEL] and vp->orig[L_HOST] pointers to struct web..

	   We presume the  newcfp  will not contain objects that oldcfp does
	   not have -- while theorethically possible, it is not supported
	   skenario..
	*/

	if (verbose) {
	  sfprintf(sfstdout,"sync_cfps() OLDVTXES =");
	  for (ovp = oldcfp->head; ovp; ovp = ovp->next[L_CTLFILE])
	    sfprintf(sfstdout," %p{%p %p}", ovp, ovp->orig[L_CHANNEL], ovp->orig[L_HOST]);
	  sfprintf(sfstdout,"\n");
	  sfprintf(sfstdout,"sync_cfps() NEWVTXES =");
	  for (nvp = newcfp->head; nvp; nvp = nvp->next[L_CTLFILE])
	    sfprintf(sfstdout," %p{%p %p}", nvp, nvp->orig[L_CHANNEL], nvp->orig[L_HOST]);
	  sfprintf(sfstdout,"\n");
	}

	ovp = oldcfp->head;
	nvp = newcfp->head;


	while (ovp != NULL && nvp != NULL) {
	  ++ovp_count;

	  /* Always prepare for removal of the ovp object..
	     Pick the next-ovp pointer now */
	  novp  = ovp->next[L_CTLFILE];
	  nnvp  = nvp->next[L_CTLFILE];

	  /* Does this exist also on NVP chain ? */

#define VTXMATCH(ovp,nvp) (((ovp)->orig[L_CHANNEL] == (nvp)->orig[L_CHANNEL]) && ((ovp)->orig[L_HOST] == (nvp)->orig[L_HOST]))

	  if (VTXMATCH(ovp, nvp)) {
	    /* Verify/adjust OVP so that OVP and NVP have same
	       address indexes in them. */
	    int i, j, id;
	    if (verbose) {
	      sfprintf(sfstdout, " OLD ngroup=%d {", ovp->ngroup);
	      for(i = 0; i < ovp->ngroup; ++i)
		sfprintf(sfstdout, " %d", ovp->index[i]);
	      sfprintf(sfstdout, " }\n");
	      sfprintf(sfstdout, " NEW ngroup=%d {", nvp->ngroup);
	      for(i = 0; i < nvp->ngroup; ++i)
		sfprintf(sfstdout, " %d", nvp->index[i]);
	      sfprintf(sfstdout, " }\n");
	    }
	    for (i = ovp->ngroup -1; i >= 0; --i) {
	      id = ovp->index[i];
	      for (j = nvp->ngroup -1; j >= 0; --j) {
		if (nvp->index[j] == id)
		  goto next_i;
	      }
	      /* ovp index elt not found in new set! */
	      for (j = i+1; j < ovp->ngroup; ++j)
		ovp->index[j-1] = ovp->index[j];
	      ovp->ngroup -= 1;
	      ovp->thread->rcpts -= 1;
	      MIBMtaEntry->sc.StoredRecipientsSc -= 1;
	    next_i:;
	    }
	    if (ovp->ngroup <= 0)
	      unvertex(ovp,-1,1); /* Don't unlink()! free() *just* ovp! */

	    ovp = novp;
	    nvp = nnvp;
	    continue;
	  }

	  if (!VTXMATCH(ovp,nvp)) {

	    struct vertex *vp;
	    int i;

	    /* Uugh... Does not match :-( */

	    vp = ovp;

	    while (vp && !VTXMATCH(vp,nvp))
	      vp = vp->next[L_CTLFILE];

	    if (vp == NULL) {
	      /* New not in old at all ??? */
	      if (verbose)
		sfprintf(sfstdout," -- NEW vertex %p NOT in OLD set!\n", nvp);
	      /* Ok, skip it, and retry with OLD vs. new NEW */
	      nvp = nnvp;
	      continue;
	    }

	    /* All OVP instances before matching NVP
	       are to be removed from OVP chains */
	    i = 0;
	    while (ovp && ovp != vp) {
	      novp = ovp->next[L_CTLFILE];

	      MIBMtaEntry->sc.StoredRecipientsSc -= vp->ngroup;
	      ovp->thread->rcpts -= vp->ngroup;
	      ovp->ngroup = 0;
	      unvertex(ovp,-1,1); /* Don't unlink()! free() *just* ovp! */

	      ++i;
	      ++ovp_count;
	      ovp = novp;
	    }
	    if (verbose)
	      sfprintf(sfstdout," -- Deleted %d OLD vertices\n", i);
	    /* Adjust NOVP variable too */
	    novp = NULL;
	    if (ovp)
	      novp = ovp->next[L_CTLFILE];
	  }

	  ovp = novp;
	  nvp = nnvp;
	}

	/* Ok,  'ovp' might be non-NULL while 'nvp' is already NULL */
	while (ovp) {
	  novp = ovp->next[L_CTLFILE];

	  MIBMtaEntry->sc.StoredRecipientsSc -= ovp->ngroup;
	  ovp->thread->rcpts -= ovp->ngroup;
	  ovp->ngroup = 0;
	  unvertex(ovp,-1,1); /* Don't unlink()! free() *just* ovp! */
	  /* Leaves CFP unharmed */

	  ovp = novp;
	}

	if (verbose)
	  sfprintf(sfstdout," -- Synced %d OLD vertices\n", ovp_count);

	oldcfp->rcpnts_failed = newcfp->rcpnts_failed;
	oldcfp->haderror |= newcfp->haderror;

	/* Now  oldcfp->head  might be NULL -> bad news.. */

	return 0;
}


void resync_file(proc, file)
	struct procinfo *proc;
	const char *file;
{
	struct stat stbuf;
	struct spblk *spl;
	long ino;
	const char *s;
	int fd;
	struct ctlfile *oldcfp, *newcfp;

	queryipccheck();

	lstat(file,&stbuf);

	s = strrchr(file,'/');
	if (s) ++s; else s = file;
	ino = atoi(s);

	/* Sometimes we may get reports of files
	   already deleted from processing.. */

	/* Already in processing ? */
	spl = sp_lookup((u_long)ino, spt_mesh[L_CTLFILE]);
	if (spl == NULL) {
#if 0
	  if (!in_dirscanqueue(NULL,ino)) {
	    sfprintf(sfstdout,"Resyncing file \"%s\" (ino=%ld)", file, ino);
	    sfprintf(sfstdout," .. not in processing database\n");
	  }
#endif
	  /* Not (anymore) in processing! */
	  return;
	}

	oldcfp = (struct ctlfile *)(spl->data);
	oldcfp->id = 0; /* Don't scramble spt_mesh[] later below */

	if (spl != NULL)
	  sp_delete(spl, spt_mesh[L_CTLFILE]);
	spl = NULL;

	++ oldcfp->resynccount;

	sfprintf(sfstdout, "Resyncing file \"%s\" (ino=%d pid=%d of=%d ho='%s') reqcnt=%d global-work-count=%ld\n",
		 file, (int) ino, proc->pid, proc->overfed,
		 (proc->ho ? proc->ho->name : "<NULL>"),
		 oldcfp->resynccount, global_wrkcnt);
	/* sfprintf(sfstdout, " .. in processing db\n"); */

	if (oldcfp->resynccount > MAXRESYNCS) {
	  /* Sigh.. Throw everything away :-( */
	  oldcfp->id = ino;
	  cfp_free(oldcfp, NULL);
	  sfprintf(sfstdout, " ... too many Resync attempts this way, throwing  it away...\n");
	  return;
	}

	/* cfp_free()->unvertex()->unctlfile() will do reinsertion */
	/* dq_insert(NULL,ino,file,31); */

	/* Now read it back! */
	fd = eopen(file, O_RDWR, 0);
	if (fd < 0) {
	  /* ???? */
	  sfprintf(sfstdout," .. FILE OPEN FAILED!\n");

	  /* Delete it from memory */
	  cfp_free(oldcfp, NULL);
	  return;
	}


	newcfp = schedule(fd, file, ino, 1); /* rereading */

	if (newcfp != NULL) {
	  /* ????  What ever, it succeeds, or it fails, all will be well */

	  sync_cfps(oldcfp, newcfp, proc);
	  newcfp->id = 0; /* Don't scramble spt_mesh[] below */

	  spl = sp_lookup((u_long)ino, spt_mesh[L_CTLFILE]);
	  if (spl)
	    sp_delete(spl, spt_mesh[L_CTLFILE]);
	  oldcfp->id = ino;
	  sp_install(oldcfp->id, (void *)oldcfp, 0, spt_mesh[L_CTLFILE]);

	  /* Delete it from memory */
	  cfp_free0(newcfp);

	  if (oldcfp->head == NULL) {
	    cfp_free(oldcfp,spl);
	    sfprintf(sfstdout," .. LOST in resync ?!  (wrkcnt %ld)\n", global_wrkcnt);
	  } else
	    sfprintf(sfstdout," .. resynced!  (wrkcnt %ld)\n", global_wrkcnt);

	} else {

	  /* Sigh.. Throw everything away :-( */
	  oldcfp->id = ino;
	  cfp_free(oldcfp, NULL);

	  sfprintf(sfstdout," .. NOT resynced!  (wrkcnt %ld)\n", global_wrkcnt);
	}
}



void receive_notify(fd)
	int	fd;
{
	char buf[1000], *s, *file;
	int i, ok, cnt;
	u_long ino;

	/* 10 receives at the time AT MOST */
	for (cnt=10;cnt;--cnt) {

	  i = recvfrom(fd, buf, sizeof(buf), 0, NULL, NULL);
	  if (i <= 0 && errno != EINTR) return;
	  if (i < 0) continue;

	  if (i >= sizeof(buf)) i = sizeof(buf)-1;
	  buf[i] = 0;

	  /* The only supported notify is:
	       "NEW X/Y/file-name"
	     message */


	  if (strncmp(buf,"NEW ",4) != 0) continue;

	  file = s = buf+4;
	  ok = 0;

	  if ('1' <= s[0] && s[0] <= '9' && strchr(s, '/') == NULL) {
	    ok = 1;
	  } else  if ('A' <= s[0] && s[0] <= 'Z' && s[1] == '/') {
	    s += 2;
	    if ('1' <= s[0] && s[0] <= '9' && strchr(s, '/') == NULL) {
	      ok = 1;
	    } else  if ('A' <= s[0] && s[0] <= 'Z' && s[1] == '/') {
	      s += 2;
	      if ('1' <= s[0] && s[0] <= '9' && strchr(s, '/') == NULL) {
		ok = 1;
	      }
	    }
	  }

	  ino = atol(s);

#if 0
	  sfprintf(sfstderr,"SCH-NOTIFY: len=%d '%s' file='%s', ino=%ld ok=%d\n",
		   i, buf, file, ino, ok);
	  zsyslog((LOG_INFO, "Got notify: '%s'", buf));
#endif

	  if (!ok) continue;

#if 0
	  if (lstat(file,&stbuf) != 0) continue;
	  if (!S_ISFILE(stbuf.st_mode)) continue;

	  if (in_dirscanqueue(dirq,stbuf.st_ino)) continue;
#endif

	  /* We may have this file in processing state...  */
	  {
	    struct spblk *spl;
	    spl = sp_lookup(ino, spt_mesh[L_CTLFILE]);
	    if (spl != NULL) {
	      /* Already in processing, don't touch.. */
	      printf("File: '%s' active (not previously locked)\n", buf+4);
	      continue;
	    }
	  }

	  dq_insert(dirq, ino, buf+4, -1);
	}
} 




/*
 * The schedule() function is in charge of reading the control file from
 * the scheduler directory, and creating all the appropriate links to the
 * control file.
 * Since it is convenient to do so here, it also goes through the list
 * of transport directives and schedules the appropriate things to be
 * done at the appropriate time in the future.
 */
static struct ctlfile *schedule(fd, file, ino, reread)
	int fd;
	const char *file;
	long ino;
	const int reread;
{
	struct ctlfile *cfp;
	struct vertex *vp;

	/* read and process the control file */
	cfp = vtxprep(slurp(fd, ino), file, reread);
	if (cfp == NULL) {
	  if (!vtxprep_skip) {	/* Unless skipped.. */
	    /* debug thing to be visible at truss/strace/whatnot */
	    eunlink(file,"sch-sch-done");	/* everything here has been processed */
	    if (verbose)
	      sfprintf(sfstdout,"completed, unlink %s\n",file);
	    return NULL;
	  }
	  vtxprep_skip_any += vtxprep_skip;
	  return NULL;
	}

	if (cfp->head == NULL) {
	  unctlfile(cfp, 0); /* Delete the file.
				(decrements those counters above!) */
	  return NULL;
	}

	if (!reread) {
	  sp_install(cfp->id, (void *)cfp, 0, spt_mesh[L_CTLFILE]);

	  for (vp = cfp->head; vp != NULL; vp = vp->next[L_CTLFILE]) {
	    /* Put into the schedules */
	    vtxdo(vp, cehead, file);
	    vp->thread->rcpts += vp->ngroup;
	  }
	}

	/* Now we have no more need for the contents in core */
	if (cfp->contents != NULL) {
	  free(cfp->contents);
	  cfp->contents = NULL;
	}

	return cfp;
}

/*
 * slurp() gets in the job-descriptor file, and does initial
 *         parsing on it.
 */

struct ctlfile *
slurp(fd, ino)
	int fd;
	long ino;
{
	register char *s;
	register int i;
	char *contents;
	int *offset;
	int offsetspace;
	struct stat stbuf;
	struct ctlfile *cfp;

	if (fd < 0)
	  return NULL;
	if (efstat(fd, &stbuf) < 0) {
	  close(fd);
	  return NULL;
	}
	if (!S_ISREG(stbuf.st_mode)) {
	  close(fd);
	  return NULL;	/* XX: give error */
	}
	contents = emalloc((int)stbuf.st_size + 1);
	if (eread(fd, contents, stbuf.st_size) != stbuf.st_size) { /* slurp */
	  close(fd);
	  free(contents); /* Failed to read ?!?! */
	  return NULL;
	}
	contents[stbuf.st_size] = 0;

	cfp = (struct ctlfile *)emalloc(sizeof(struct ctlfile));
	memset((void*)cfp, 0, sizeof(struct ctlfile));

	cfp->fd       = fd;
	cfp->dirind   = -1; /* Not known -- or top-level */
	cfp->uid      = stbuf.st_uid;

	cfp->envctime = stbuf.st_ctime;
#ifdef HAVE_STRUCT_STAT_ST_ATIM_TV_NSEC
	cfp->envctimens = stbuf.st_ctim.tv_nsec;
#else
#ifdef HAVE_STRUCT_STAT_ST_ATIM___TV_NSEC
	cfp->envctimens = stbuf.st_ctim.__tv_nsec;
#else
#ifdef HAVE_STRUCT_STAT_ST_ATIMENSEC
	cfp->envctimens = stbuf.st_ctimensec;
#else
	cfp->envctimens = 0;
#endif
#endif
#endif


	cfp->contents = contents;

	/* 
	   cfp->vfpfn    = NULL;
	   cfp->spoolid  = NULL;
	   cfp->head     = NULL;
	   cfp->mark     = V_NONE;
	   cfp->haderror = 0;
	   cfp->mid      = NULL;
	   cfp->envid    = NULL;
	   cfp->logident = NULL;
	   cfp->erroraddr = NULL;
	   cfp->msgbodyoffset = 0;
	 */

	/* go through the file and mark it off */
	i = 0;
	offsetspace = 100;
	offset = (int*)emalloc(sizeof(int)*offsetspace);
	offset[i++] = 0L;
	for (s = contents; s - contents < stbuf.st_size; ++s) {
	  if (*s == '\n') {
	    *s++ = '\0';
	    if (s - contents < stbuf.st_size) {
	      if (i >= offsetspace-1) {
		offsetspace += 20;
		offset = (int*)erealloc(offset,sizeof(int)*offsetspace);
	      }
	      offset[i++] = s - contents;
	      if (*s == _CF_MSGHEADERS ||
		  *s == _CF_MIMESTRUCT) {
		/* find a \n\n combination */
		while (!(*s == '\n' && *(s+1) == '\n'))
		  if (s-contents < stbuf.st_size)
		    ++s;
		  else
		    break;
		if (s - contents >= stbuf.st_size) {
		  /* XX: header ran off file */
		}
	      } else if (*s == _CF_BODYOFFSET) {
		cfp->msgbodyoffset = atoi(s+2);
	      } else if (*s == _CF_DSNENVID) {
		/* cfp->envid = strsave(s+2); */
	      } else if (*s == _CF_DSNRETMODE) {
		/* cfp->dsnretmode = strsave(s+2); */
	      } else if (*s == _CF_MESSAGEID) {
		/* cfp->mid = strsave(s+2); */
	      } else if (*s == _CF_LOGIDENT) {
		/* cfp->logident = strsave(s+2); */
	      } else if (*s == _CF_ERRORADDR) {
		/* cfp->erroraddr = strsave(s+2); */
	      } else if (*s == _CF_TURNME) {
		/* Umm... it is a bit complex */
		/* sfprintf(sfstdout,"An ETRN request for target '%s'\n",s+2); */
	      }
	    }
	  }
	}
	cfp->nlines = i;
	/* closing fd must be done in vtxprep(), so we can unlock stuff easy */
	cfp = (struct ctlfile *)erealloc((void*)cfp,
					 (u_int) (sizeof(struct ctlfile) +
						  i * (sizeof offset[0])));
	if (cfp) {
	  /* copy over the offsets */
	  memcpy(&(cfp->offset[0]), offset, sizeof(offset[0]) * i);

	  cfp->id = ino;
	  /* cfp->mid = NULL; */

	  /* INC there in every case! */
	  ++global_wrkcnt;
	  ++MIBMtaEntry->sc.StoredMessagesSc;

	} else {
	  /* realloc() failed.. */
	  free(contents);
	}

	free(offset);	/* release the block */
	return cfp;
}

struct offsort {
	int	offset;
	int	myidx;
	int	headeroffset;
	int	drptoffset;
	int	delayslot;
	int	notifyflg;
	char	*sender;
	/* char	*dsnrecipient; */
	/* time_t	wakeup; */
	time_t	deadline; /* Deliver BY= parameter */
};

/* ``bcfcn'' is used by the qsort comparison routine,
   bcp points to the control file bytes
 */

static char *bcp;

static int bcfcn __((const void *, const void *));
static int bcfcn(a, b)
     const void *a, *b;
{
	const struct offsort *aa = a, *bb = b;
	return strcmp(bcp + aa->offset, bcp + bb->offset);
}


static int
lockverify(cfp,cp,verbflg)	/* Return 1 when lock process does not exist */
	struct ctlfile *cfp;	/* Call only when the lock is marked active! */
	const char *cp;
	const int verbflg;
{
	char	lockbuf[1+_CFTAG_RCPTPIDSIZE];
	int	lockpid;
	int	sig = 0;

#if 0
# ifdef SIGCONT	/* OSF/1 acts differently if we use SIGNAL 0 :-( */
	sig = SIGCONT;
# endif
#endif

	++cp;
	if (!(*cp == ' ' ||
	      (*cp >= '0' && *cp <= '9'))) return 1; /* Old-style entry */
	memcpy(lockbuf,cp,_CFTAG_RCPTPIDSIZE);
	lockbuf[sizeof(lockbuf)-1] = 0;
	if (sscanf(lockbuf,"%d",&lockpid) != 1) return 1; /* Bad value ? */
	if (kill(lockpid,sig) != 0) return 1; /* PID does not exist, or
					       other error.. */
	if (verbflg)
	  sfprintf(sfstderr,"lockverify: Lock with PID=%d is active on %s:%s\n",
		   lockpid, cfp->mid, cp+_CFTAG_RCPTPIDSIZE);
	return 0;	/* Locking PID does exist.. */
}


/*
 *  The  vtxprep() does deeper analysis on jobs described at the file.
 *  It verifies possible locks (if they are still valid), and gathers
 *  all of the information regarding senders and recipients.
 *
 *  All "recipient"-lines are sorted to ease searching of vertices with
 *  identical channel, and host definitions.  If there are more than one
 *  recipient with given (channel, host)-tuple, all such recipients are
 *  wrapped into same vertex node with its respective ``recipient group''.
 *
 */
static struct ctlfile *vtxprep(cfp, file, rereading)
	struct ctlfile *cfp;
	const char *file;
	const int rereading;
{
	register int i, opcnt;
	register int *lp;
	int svn;
	int c_echannel, c_ehost, c_l_echannel, c_l_ehost;
	char *cp, *channel, *host, *l_channel, *l_host;
	char *echannel, *ehost, *l_echannel, *l_ehost, mfpath[100], flagstr[2];
	char *latest_sender = NULL;
	char *senderchannel = NULL;
	struct vertex *vp, *pvp, **pvpp, *head;
	struct stat stbuf;
	struct offsort *offarr;
	int offspc, mypid;
	int prevrcpt = -1;
	int is_turnme = 0;
	/* time_t wakeuptime; */
	long format = 0;

	char fpath[128], path[128], path2[128];

	if (cfp == NULL)
	  return NULL;

	mytime(&now);

	strcpy(fpath, file);

	channel = host = NULL;

	/* copy offsets into local array */
	offspc = 16;
	offarr = (struct offsort *)emalloc(offspc * sizeof(struct offsort));

	if (!offarr) {
	  /* malloc() failure.. */
	  sfprintf(sfstderr,"malloc failed, discarding job: '%s'\n", file);
	  cfp_free(cfp, NULL);
	  return NULL;
	}


	mypid = getpid();
	opcnt = 0;
	svn = 0;
	vtxprep_skip = 0;
	lp = &cfp->offset[0];
	for (i = 0; i < cfp->nlines; ++i, ++lp) {
	  cp = cfp->contents + *lp + 1;
	  /* wakeuptime = 0; */
	  if (*cp == _CFTAG_LOCK) {
	    /*
	     * This can happen when we restart the scheduler, and
	     * some previous transporter is still running.
	     * (and DEFINITELY during resync! when we simply ignore locks)
	     */
	    if (!lockverify(cfp, cp, !rereading)) {
#if 1
	      long ino = 0;
	      /*
	       * IMO we are better off by forgetting for a while that
	       * this spool-file exists at all.  Thus very least we
	       * won't errorneously delete it.
	       */
	      close(cfp->fd);	/* Was opened on  schedule() */
	      if (cfp->vfpfn != NULL) {
		Sfio_t *vfp = vfp_open(cfp);
		if (vfp) {
		  sfprintf(vfp,
			   "scheduler: Skipped a job-file because it is held locked by PID=%6.6s\n",cp+1);
		  sfclose(vfp);
		}
	      }
	      sfprintf(sfstderr,
		       "scheduler: Skipped a job-file because it is held locked by PID=%6.6s\n",cp+1);

	      cfp_free(cfp, NULL);
	      ++vtxprep_skip;
	      ++vtxprep_skip_lock;
	      free(offarr);

	      /* XXX: Should we  dq_insert()  this back in ?
		      Or do we let the occasional recursive
		      scanner to check things deeply ? */
	      cp = strrchr(file,'/');
	      if (cp) ino = atol(cp+1); else ino = atol(file);
	      dq_insert(dirq, ino, file, 32);

	      return NULL;
#else
	      /* We can't simply forget this, we must do something
		 smarter -- We use approach of marking the vertex
		 non-startable until one hour from now. */
	      wakeuptime = now + 3600; /* 1 hour */
#endif
	    } else {
	      if (*cp != _CFTAG_NORMAL) {
		*cp = _CFTAG_NORMAL; /* unlock it */
		lockaddr(cfp->fd, NULL, (long) (cp - cfp->contents),
			 _CFTAG_LOCK, _CFTAG_NORMAL, cfp->mid,
			 cp+_CFTAG_RCPTPIDSIZE, mypid);
	      }
	    }
	  }
	  /* Calculate summary info */
	  if (cp[-1] == _CF_RECIPIENT) {
	    ++cfp->rcpnts_total;
	    if (*cp == _CFTAG_NOTOK) {
#if 0
	      ++cfp->rcpnts_failed;
	      ++MIBMtaEntry->sc.ReceivedRecipientsSc,
	      ++MIBMtaEntry->sc.TransmittedRecipientsSc;
#endif
	      prevrcpt = -1;
	    } else if (*cp != _CFTAG_OK) {
	      ++cfp->rcpnts_work;
	    } else { /* _CFTAG_OK */
#if 0
	      ++MIBMtaEntry->sc.ReceivedRecipientsSc,
	      ++MIBMtaEntry->sc.TransmittedRecipientsSc;
#endif
	    }
	  }
	  if (*cp == _CFTAG_NORMAL ||
	      (rereading && *cp == _CFTAG_LOCK) ||
	      *cp == '\n' /* This appears for msg-header entries.. */ ) {
	    ++cp;
	    switch (cp[-2]) {
	    case _CF_FORMAT:
	      sscanf(cp,"%li",&format);
	      if (format & (~_CF_FORMAT_KNOWN_SET)) {

		sfprintf(sfstderr,"%s: ** FILE: '%s' has unknown/unsupported format set: 0x%08lx !\n",
			 progname, file, format);

		cfp_free(cfp, NULL);
		free(offarr);
		return NULL;
	      }
	      cfp->format = format;
	      break;
	    case _CF_SENDER:
	      while (*cp == ' ') ++cp;
	      senderchannel = cp;
	      while (*cp != 0 && *cp != ' ') ++cp; 
	      if (*cp == ' ') *cp++ = 0;
	      while (*cp == ' ') ++cp;
	      /* Scan over the sender 'host' */
	      cp = skip821address(cp);
	      while (*cp == ' ') ++cp;
	      /* Scan over the sender 'user' */
	      latest_sender = cp;
	      cp = skip821address(cp);
	      *cp = 0;
	      if (cfp->erroraddr)  free(cfp->erroraddr);
	      cfp->erroraddr = strsave(latest_sender);
	      if (strcmp(senderchannel,"error")==0) {
		cfp->iserrmesg = 1;
		cfp->erroraddr[0] = 0; /* Make it '<>' */
	      } break;
	    case _CF_RECIPIENT:
	      if (opcnt >= offspc-1) {
		offspc *= 2;
		offarr = (struct offsort *)erealloc(offarr,
						    sizeof(struct offsort) *
						    offspc);
		if (!offarr) {
		  /* realloc() failure.. */
		  sfprintf(sfstderr,"realloc() failed, discarding job: '%s'\n", file);
		  cfp_free(cfp, NULL);
		  return NULL;
		}
	      }
	      offarr[opcnt].offset = *lp + 2;
	      strlower(cp);
	      if ((format & _CF_FORMAT_TA_PID) || *cp == ' ' ||
		  (*cp >= '0' && *cp <= '9')) {
		/* New PID locking scheme.. */
		offarr[opcnt].offset += _CFTAG_RCPTPIDSIZE;
		cp += _CFTAG_RCPTPIDSIZE;
	      }
	      if ((format & _CF_FORMAT_DELAY1) || *cp == ' ' ||
		  (*cp >= '0' && *cp <= '9')) {
		/* Newer DELAY data slot - _CFTAG_RCPTDELAYSIZE bytes */
		offarr[opcnt].delayslot = offarr[opcnt].offset;
		offarr[opcnt].offset += _CFTAG_RCPTDELAYSIZE;
		cp += _CFTAG_RCPTDELAYSIZE;
	      } else
		offarr[opcnt].delayslot = 0;
	      /* offarr[opcnt].wakeup = wakeuptime; */
	      offarr[opcnt].myidx = i;
	      offarr[opcnt].headeroffset = -1;
	      offarr[opcnt].drptoffset = -1;
	      offarr[opcnt].sender = latest_sender;
	      offarr[opcnt].notifyflg = NOT_FAILURE;
	      prevrcpt = opcnt;
	      ++opcnt;

	      break;
	    case _CF_RCPTNOTARY:
	      /* IETF-NOTARY-DRPT+NOTIFY DATA! */
	      if (prevrcpt >= 0) {
		offarr[prevrcpt].drptoffset = *lp + 2;
		/* Lets parse the input, we want NOTIFY= flags */
		while (*cp != 0) {
		  while (*cp == ' ' || *cp == '\t') ++cp;
		  if (CISTREQN("NOTIFY=",cp,7)) {
		    offarr[prevrcpt].notifyflg = 0;
		    cp += 7;
		    while (*cp) {
		      if (CISTREQN(cp,"NEVER",5)) {
			cp += 5;
			offarr[prevrcpt].notifyflg |= NOT_NEVER;
		      } else if (CISTREQN(cp,"DELAY",5)) {
			cp += 5;
			offarr[prevrcpt].notifyflg |= NOT_DELAY;
		      } else if (CISTREQN(cp,"FAILURE",7)) {
			cp += 7;
			offarr[prevrcpt].notifyflg |= NOT_FAILURE;
		      } else if (CISTREQN(cp,"SUCCESS",7)) {
			cp += 7;
			offarr[prevrcpt].notifyflg |= NOT_SUCCESS;
		      } else if (CISTREQN(cp,"TRACE",  5)) {
			cp += 5;
			offarr[prevrcpt].notifyflg |= NOT_TRACE;
		      } else {
			break; /* Burp ?? */
		      }
		      if (*cp == ',') ++cp;
		    }
		  } else if (CISTREQN("BY=",cp,7)) {
		    /* FIXME: Parse the BY= parameter! */
		    while (*cp && *cp != ' ' && *cp != '\t') ++cp;
		  } else {
		    while (*cp && *cp != ' ' && *cp != '\t') ++cp;
		  }
		}
	      }
	      prevrcpt = -1; /* Add ONCE! */
	      break;
	    case _CF_MSGHEADERS:
	      for (/* we count up.. */; svn < opcnt; ++svn)
		offarr[svn].headeroffset = *lp + 2;
	      break;
	    case _CF_DSNRETMODE:
	      if (cfp->dsnretmode) free(cfp->dsnretmode);
	      cfp->dsnretmode = strsave(cp);
	      break;
	    case _CF_DSNENVID:
	      if (cfp->envid) free(cfp->envid); /* shouldn't happen.. */
	      cfp->envid = strsave(cp);
	      break;
	    case _CF_DIAGNOSTIC:
	      cfp->haderror = 1;
	      break;
	    case _CF_MESSAGEID:
	      if (cfp->mid != NULL) free(cfp->mid); /* shouldn't happen.. */
	      cfp->mid = strsave(cp);
	      break;
	    case _CF_BODYOFFSET:
	      cfp->msgbodyoffset = atoi(cp);
	      break;
	    case _CF_LOGIDENT:
	      if (cfp->logident) free(cfp->logident); /* shouldn't happen..*/
	      cfp->logident = strsave(cp);
	      break;
	    case _CF_ERRORADDR:
	      if (cfp->erroraddr) free(cfp->erroraddr); /* could happen */
	      cfp->erroraddr = strsave(cp);
	      break;
	    case _CF_OBSOLETES:
	      deletemsg(cp, cfp);
	      break;
	    case _CF_VERBOSE:
	      cfp->vfpfn = strsave(cp);
	      break;
	    case _CF_TURNME:
	      sfprintf(sfstdout,"%s ETRN: %s\n", timestring(), cp);
	      strlower(cp);
	      turnme(cp);
	      is_turnme = 1;
	      break;
	    }
	  }
	}
	close(cfp->fd);	/* closes the fd opened in schedule() */

	if (fpath[0] >= 'A') {
	  /* Prefixed with a subdir path */
	  int hash = 0;
	  char *s = fpath;

	  while (*s >= 'A' && *s <= 'Z') {
	    hash <<= 8;
	    hash |= (*s) & 0xff;
	    ++s;
	    if (*s != '/') break;
	    ++s;
	  }
	  cfp->dirind = hash;

	} else { /* Not at subdirs */

	  if (cfp->mid && hashlevels > 0) {
	    /* We have a desire to use subdirs, now the magic of hashing
	       into subdirs...  inode number ? */

	    int hash, rc;

	    if (hashlevels > 1) {
	      hash = atol(cfp->mid) % (26*26);
	      hash = (('A' + hash / 26) << 8) | ('A' + hash % 26);
	    } else {
	      hash = (atol(cfp->mid) % 26) + 'A';
	    }
	    cfp->dirind = hash;
	    /* Ok, we have the hash values, now move the file
	       to match with our hashes.. */
	    sprintf(path, "%s%s", cfpdirname(hash), fpath);
	    
	    while ((rc = rename(fpath, path)) != 0) {
	      if (errno != EINTR) break;
	    }
	    if (rc != 0) {
	      /* Failed, why ? */
	      if (errno != ENOENT) {
		/* For any other than 'no such (target) directory' */
		cfp->dirind = -1;
	      } else {
		cfp_mksubdirs("",cfpdirname(hash));
		while ((rc = rename(fpath, path)) != 0) {
		  if (errno != EINTR) break;
		}
		if (rc != 0)
		  cfp->dirind = -1; /* Failed for any reason */
		else
		  strcpy(fpath, path);
	      }
	    } else
	      strcpy(fpath, path);

	    if (cfp->dirind >= 0) {
	      /* Successfully renamed the transport file to a subdir,
		 now do the same to the queue directory! */
	      sprintf(path,  "../%s/%s", QUEUEDIR, cfp->mid);
	      sprintf(path2, "../%s/%s%s",
		      QUEUEDIR, cfpdirname(cfp->dirind), cfp->mid);

	      while ((rc = rename(path, path2)) != 0) {
		if (errno != EINTR) break;
	      }
	      if (rc != 0) {
		if (errno == ENOENT) {
		  /* No dirs ?? */
		  cfp_mksubdirs(QUEUEDIR,cfpdirname(hash));
		  while ((rc = rename(path, path2)) != 0) {
		    if (errno != EINTR) break;
		  }
		}
	      }
	      /* If failed, it will be reported below */
	    }
	  }
	}

	if (cfp->mid != NULL) {
	  if (cfp->dirind >= 0)
	    sprintf(mfpath, "../%s/%s%s",
		    QUEUEDIR, cfpdirname(cfp->dirind), cfp->mid);
	  else
	    sprintf(mfpath, "../%s/%s", QUEUEDIR, cfp->mid);
	}
	if (cfp->mid == NULL || cfp->logident == NULL ||
	    estat(mfpath, &stbuf) < 0) {
	  if (!is_turnme) {
	    Sfio_t *vfp = vfp_open(cfp);
	    if (vfp) {
	      sfprintf(vfp, "aborted due to missing information\n");
	      sfclose(vfp);
	    }
	  }
	  cfp_free(cfp, NULL);
	  free(offarr);
	  return NULL;
	}
	cfp->mtime = stbuf.st_mtime; /* instead of ctime, we use mtime
					at the queue-dir accesses, this
					way we can move the spool to
					another machine, and run things
					in there, and still have same
					expiration times.. */
#ifdef HAVE_STRUCT_STAT_ST_ATIM_TV_NSEC
	cfp->mtimens = stbuf.st_mtim.tv_nsec;
#else
#ifdef HAVE_STRUCT_STAT_ST_ATIM___TV_NSEC
	cfp->mtimens = stbuf.st_mtim.__tv_nsec;
#else
#ifdef HAVE_STRUCT_STAT_ST_ATIMENSEC
	cfp->mtimens = stbuf.st_mtimensec;
#else
	cfp->mtimens = 0;
#endif
#endif
#endif

	/* Reuse the buffer ...
	   Generate same spoolid string that all other subsystems also
	   report to syslog. */

	taspoolid(path2, cfp->id, cfp->mtime, cfp->mtimens);

	cfp->spoolid = strsave(path2);
	if (!cfp->spoolid) {
	  /* malloc() failure.. */
	  sfprintf(sfstderr,"malloc() failed, discarding job: '%s'\n", file);
	  cfp_free(cfp, NULL);
	  free(offarr);
	  return NULL;
	}

	cfp->fd = -1;
	/* sort it to get channels and channel/hosts together */
	bcp = cfp->contents;
	if (opcnt > 1)
	  qsort((char *)offarr, opcnt, sizeof (struct offsort), bcfcn);
	/*
	 * Loop through them; whenever either channel or host changes,
	 * make a new vertex. All such vertices must be linked together.
	 */
	strcpy(flagstr," ");
	l_channel = l_echannel = l_host = l_ehost = flagstr;
	c_echannel = c_ehost = c_l_echannel = c_l_ehost = 0;
	svn = 0;
	pvp = NULL;
	head = NULL;
	pvpp = &head;
	for (i = 0; i < opcnt; ++i) {
	  channel = bcp + offarr[i].offset /* - 2 */;
	  while (*channel == ' ') ++channel; /* Skip possible space(s) */
	  host = echannel = skip821address(channel);
	  c_l_echannel = *host; if (c_l_echannel) *host++ = '\0';
	  while (*host == ' ') ++host; /* Skip space(s) */
#if 1
	  /* [mea]   channel ((mx.target)(mx.target mx.target)) rest.. */
	  cp = host;
	  if (*cp == '(') {
	    while(*cp == '(')
	      ++cp;
	    while(*cp && *cp != ' ' && *cp != '\t' && *cp != ')')
	      ++cp;
	    if (*cp)
	      ehost = cp;
	    else
	      continue;		/* error! */
	    /* Ok, found ehost, now parsing past parenthesis.. */
	    cp = host;
	    while(*host == '(')  ++host;
	    if (*cp == '(') {
	      ++cp;
	      while(*cp == '(') {
		/* Find ending ')', and skip it */
		while(*cp && *cp != ')') ++cp;
		if (*cp == ')') ++cp;
	      }
	      /* Ok, scanned past all inner parenthesis, now ASSUME
		 next one is ending outer parenthesis, and skip it */
	      ++cp;
	    }
	    if (*cp != ' ' && *cp != '\t')
	      continue;		/* Not proper separator.. error! */
	  } else
#endif
	    {
	      ehost = skip821address(host);
	      strlower(host);
	      if (ehost == NULL || ehost == host) /* error! */
		continue;
	    }

	  c_ehost = *ehost; *ehost = '\0';
	  /* compare with the last ones */
	  if (strcmp(channel, l_channel) || strcmp(host, l_host)) {
	    /* wrap and tie the old vertex node */
	    if (i != svn) {
	      u_int alloc_size = (u_int) (sizeof (struct vertex) +
					  (i - svn - 1) * sizeof (int));
	      vp = (struct vertex *)emalloc(alloc_size);
	      if (!vp) {
		/* malloc() failure.. */
		sfprintf(sfstderr,"malloc() failed, discarding job: '%s'\n", file);
		cfp_free(cfp, NULL);
		free(offarr);
		return NULL;
	      }
	      MIBMtaEntry->sc.StoredVerticesSc += 1;

	      memset((char*)vp, 0, alloc_size);
	      vp->cfp             = cfp;
	      vp->next[L_CTLFILE] = NULL;
	      vp->prev[L_CTLFILE] = pvp;
#if 0
	      vp->thread          = NULL;
	      vp->web[L_CTLFILE]  = NULL;
	      vp->message         = NULL;
	      vp->retryindex      = 0;
	      vp->nextitem        = NULL;
	      vp->previtem        = NULL;
	      vp->proc            = NULL;
	      vp->attempts        = 0;
	      vp->notary          = NULL;
#endif
	      vp->ngroup       = i - svn;
	      MIBMtaEntry->sc.StoredRecipientsSc   += vp->ngroup;
	      MIBMtaEntry->sc.ReceivedRecipientsSc += vp->ngroup;

	      /* vp->sender       = strsave(offarr[svn].sender); */
	      /* vp->wakeup       = offarr[svn].wakeup; */
	      vp->headeroffset = offarr[svn].headeroffset; /*They are similar*/
	      vp->drptoffset   = offarr[svn].drptoffset;
	      vp->notaryflg    = offarr[svn].notifyflg;
	      while (svn < i) {
		vp->index[i-svn-1] = offarr[svn].myidx;
		++svn;
	      }
	      *pvpp = vp;
	      pvpp = &vp->next[L_CTLFILE];
	      pvp = vp;
	      link_in(L_HOST,    vp, l_host);
	      link_in(L_CHANNEL, vp, l_channel);
	    }
	    /* create a new vertex node */
	    svn = i;
	  }
	  /* stick the current 'r'ecipient  line into the current vertex */
	  /* restore the characters */
	  *l_echannel  = c_l_echannel;
	  *l_ehost     = c_l_ehost;
	  l_echannel   = echannel;
	  l_ehost      = ehost;
	  c_l_echannel = c_echannel;
	  c_l_ehost    = c_ehost;
	  l_channel    = channel;
	  l_host       = host;
	} /* for( .. i < opcnt .. ) */

	/* wrap and tie the old vertex node (this is a copy of code above) */
	if (i != svn) {
	  u_int alloc_size = (u_int) (sizeof (struct vertex) +
				      (i - svn - 1) * sizeof (int));
	  vp = (struct vertex *)emalloc(alloc_size);
	  if (!vp) {
	    /* malloc() failure.. */
	    sfprintf(sfstderr,"malloc() failed, discarding job: '%s'\n", file);
	    cfp_free(cfp, NULL);
	    free(offarr);
	    return NULL;
	  }
	  MIBMtaEntry->sc.StoredVerticesSc += 1;

	  memset((void*)vp, 0, alloc_size);
	  vp->cfp = cfp;
	  vp->next[L_CTLFILE] = NULL;
	  vp->prev[L_CTLFILE] = pvp;
#if 0
	  vp->message = NULL;
	  vp->retryindex = 0;
	  vp->nextitem = NULL;
	  vp->previtem = NULL;
	  vp->proc = NULL;
	  vp->attempts     = 0;
	  vp->notary       = NULL;
#endif
	  vp->ngroup = i - svn;
	  MIBMtaEntry->sc.StoredRecipientsSc   += vp->ngroup;
	  MIBMtaEntry->sc.ReceivedRecipientsSc += vp->ngroup;

	  /* vp->sender = strsave(offarr[snv].sender); */
	  /* vp->wakeup       = offarr[svn].wakeup; */
	  vp->headeroffset = offarr[svn].headeroffset; /* Just any of them will do */
	  vp->drptoffset = offarr[svn].drptoffset;
	  vp->notaryflg  = offarr[svn].notifyflg;
	  while (svn < i) {
	    vp->index[i-svn-1] = offarr[svn].myidx;
	    ++svn;
	  }
	  *pvpp = vp;
	  pvpp = &vp->next[L_CTLFILE];
	  pvp = vp;
	  link_in(L_HOST, vp, host);
	  link_in(L_CHANNEL, vp, channel);
	}

	*l_echannel = c_l_echannel;
	*l_ehost    = c_l_ehost;

	/*
	   for (vp = head; vp != NULL; vp = vp->next[L_CTLFILE]) {
	     sfprintf(sfstdout,"--\n");
	     for (i = 0; i < vp->ngroup; ++i)
	       sfprintf(sfstdout,"\t%s\n", cfp->contents+cfp->offset[vp->index[i]]);
	   }
	*/

	cfp->head = head;
	free(offarr);
	if (verbose) {
	  int completed = cfp->rcpnts_total - cfp->rcpnts_work -
			  cfp->rcpnts_failed;
	  sfprintf(sfstdout,"vtxprep: msg %s rcptns total %d work %d failed %d done %d\n  vertices:",
		 cfp->mid, cfp->rcpnts_total, cfp->rcpnts_work,
		 cfp->rcpnts_failed, completed );
	  vp = cfp->head;
	  for (vp = cfp->head; vp; vp = vp->next[L_CTLFILE]) {
	    sfprintf(sfstdout," %p", vp);
	  }
	  sfprintf(sfstdout,"\n");
	}

	{
	  Sfio_t *vfp = vfp_open(cfp);
	  if (vfp) {
	    if (cfp->mid) sfprintf(vfp, "scheduler processing %s\n", cfp->mid);
	    sfclose(vfp);
	  }
	}

	return cfp;
}

/*
 *  The  vtxmatch()  is a subroutine to  vtxdo()  matching for
 *  scheduler definition entries from the scheduler configuration table.
 *
 */

static int vtxmatch(vp, tp)
	struct vertex *vp;
	struct config_entry *tp;
{
	/* if the channel doesn't match, there's no hope! */
	if (verbose>1)
	  sfprintf(sfstdout,"ch? %s %s\n", vp->orig[L_CHANNEL]->name, tp->channel);
	if (tp->channel[0] == '*' && tp->channel[1] == '\0')
	  return 0; /* Never match the defaults entry! */
	if (!globmatch(tp->channel, vp->orig[L_CHANNEL]->name))
	  return 0;

	if (!(tp->host == NULL || tp->host[0] == '\0' ||
	      (tp->host[0] == '*' && tp->host[1] == '\0'))) {
	  if (!globmatch(tp->host, vp->orig[L_HOST]->name))
	    return 0;
	}

	if (verbose>1)
	  sfprintf(sfstdout,"host %s %s\n", vp->orig[L_HOST]->name, tp->host);

	return 1;
}

static void ce_fillin __((struct threadgroup *, struct config_entry *));
static void ce_fillin(thg,cep)
	struct threadgroup *thg;
	struct config_entry *cep;
{
	struct config_entry *ce = &(thg->ce);

	defaultconfigentry( ce,cep );

	if (cep->interval != -1) ce->interval = cep->interval;
	if (cep->idlemax  != -1) ce->idlemax  = cep->idlemax;
	if (cep->expiry   != -1) ce->expiry   = cep->expiry;
	if (cep->expiry2  != -1) ce->expiry2  = cep->expiry2;
	ce->expiryform     = cep->expiryform;
	if (cep->uid      != -1) ce->uid = cep->uid;
	if (cep->gid      != -1) ce->gid = cep->gid;
	if (cep->maxkids  != -1) ce->maxkids = cep->maxkids;
	if (cep->maxkidChannel != -1) ce->maxkidChannel = cep->maxkidChannel;
	if (cep->maxkidThreads != -1) ce->maxkidThreads = cep->maxkidThreads;
	if (cep->nretries > 0) {
	  ce->nretries = cep->nretries;
	  ce->retries  = cep->retries;
	}
	if (cep->command != NULL) {
	  ce->command = cep->command;
	  ce->argv    = cep->argv;
	}
	ce->flags |= cep->flags; /* XX: Grumble.. additive only.. */
	ce->host   = cep->host;
	if (cep->skew > 0) ce->skew = cep->skew;

	if (ce->interval == -1)
	  ce->interval = 3600;
	if (ce->idlemax == -1)
	  ce->idlemax = ce->interval * 3;
	if (ce->maxkids == -1)
	  ce->maxkids = global_maxkids;
	if (ce->maxkidChannel == -1)
	  ce->maxkidChannel = global_maxkids;
	if (ce->maxkidThreads == -1)
	  ce->maxkidThreads = global_maxkids;
}


/*
 *  The  vtxdo()  tries thru all scheduler configuration entries
 *  looking for a matching one which to fill in for the input vertex.
 *
 *  In the end it calls  reschedule()  to place the vertex into scheduling
 *  queues (threads)
 *
 */

static void vtxdo(vp, cehdr, path)
	struct vertex *vp;
	struct config_entry *cehdr;
	const char *path;
{
	struct config_entry *tp;
	int n;
	int cnt = 0;

	/*
	 * go through scheduler control file entries and
	 * fill in the blanks in the vertex specification
	 */
	n = 0;
	for (tp = cehdr; tp != NULL; tp = tp->next) {
	  ++cnt;
	  if (vtxmatch(vp, tp)) {
	    /* tp points to the selected config entry */
	    n = 1;
	    break;
	  }
	}
	if (n == 0) {
	  sfprintf(sfstderr, "%s: no pattern matched %s/%s address %s%s\n",
		   progname, vp->orig[L_CHANNEL]->name,vp->orig[L_HOST]->name,
		   path ? "file=":"", path);
	  /* XX: memory leak here? */
	  return;
	}
	if (verbose)
	  sfprintf(sfstdout, "Matched %dth config entry with: %s/%s\n", cnt,
		   vp->orig[L_CHANNEL]->name, vp->orig[L_HOST]->name);

	/* set default values */
	if (tp->expiry > 0)
	  vp->ce_expiry = tp->expiry + vp->cfp->mtime;
	else
	  vp->ce_expiry = 0;

	if (tp->expiry2 > 0 && tp->expiry > 0)
	  vp->ce_expiry2 = tp->expiry2 + vp->ce_expiry;
	else
	  vp->ce_expiry2 = /* vp->ce_expiry */ 0;

	if (vp->ce_expiry2 < vp->ce_expiry)
	  vp->ce_expiry2 = vp->ce_expiry + 24*3600;

	if (tp->reporttimes[0])
	  vp->nextrprttime = now + tp->reporttimes[0];
	else
	  vp->nextrprttime = now + global_report_interval;

	thread_linkin(vp,tp,cnt,ce_fillin);

	if (verbose>1)
	  vtxprint(vp);
}


int vtxredo(p, spl)
	void *p;
        struct spblk *spl;
{
        struct ctlfile *cfp = (struct ctlfile *)spl->data;
	struct vertex *vp;

        /* assert cfp != NULL */
	for (vp = cfp->head ; vp != NULL ; vp = vp->next[L_CTLFILE]) {
	  vtxdo(vp, p /* -> rrcf_head */, NULL);
	}
        return 0;
}


/* Shell-GLOB-style matching */
static int globmatch(pattern, string)
	register const char	*pattern;
	register const char	*string;
{
	while (1) {
	  switch (*pattern) {
	  case '{':
	    {
	      const char *p = pattern+1;
	      const char *s = string;

	      /* This matches at the END of the pattern:  '*.{fii,foo,faa}' */

	      for ( ; *p != 0 && *p != '}'; ++p) {
		if (*p == ',') {
		  if (*s == '\0')
		    return 1; /* We have MATCH! */
		  s = string;
		  continue;
		}
		if (*s != *p) {
		  /* Not the same .. */
		  s = string;
		  /* Ok, perhaps next pattern segment ? */
		  while (*p != '\0' && *p != '}' && *p != ',')
		    ++p;
		  if (*p != ',')
		    return 0; /* No next pattern ?
				 We definitely have no match! */
		  continue;
		}
		if (*s != 0)
		  ++s;
	      }
	      if (*p == '\0' || *p == '}')
		if (*s == 0)
		  return 1;
	      return 0;

	    }
	    break;
	  case '*':
	    ++pattern;
	    if (*pattern == 0) {
	      /* pattern ended with '*', we can accept any string trail.. */
	      return 1;
	    }
	    /* We do 'common case' optimization here, but will loose some
	       performance, if somebody gives '*foo*' as a pattern.. */
	    {
	      const char *p = pattern;
	      int i = 0, c;
	      while ((c = *p++) != 0) {
		/* Scan for special chars in pattern.. */
		if (c == '*' || c == '[' || c == '{' || c == '\\' || c == '?'){
		  i = 1; /* Found! */
		  break;
		}
	      }
	      if (!i) { /* No specials, match from end of string */
		int len = strlen(string);
		i = strlen(pattern);
		if (i > len) return 0; /* Tough.. pattern longer than string */
		if (memcmp(string + len - i, pattern, i) == 0)
		  return 1; /* MATCH! */
	      }
	    }
	    do {
	      if (globmatch(pattern, string))
		return 1;
	    } while (*string++ != '\0');
	    return 0;
	  case '\\':
	    ++pattern;
	    if (*pattern == 0 ||
		*pattern != *string)
	      return 0;
	    break;
	  case '[':
	    if (*string == '\0')
	      return 0;
	    if (*(pattern+1) == '^') {
	      ++pattern;
	      while ((*++pattern != ']')
		     && (*pattern != *string))
		if (*pattern == '\0')
		  return 0;
	      if (*pattern != ']')
		return 0;
	      string++;
	      break;
	    }
	    while ((*++pattern != ']') && (*pattern != *string))
	      if (*pattern == '\0')
		return 0;
	    if (*pattern == ']')
	      return 0;
	    while (*pattern++ != ']')
	      if (*pattern == '\0')
		return 0;
	    string++;
	    break;
	  case '?':
	    ++pattern;
	    if (*string++ == '\0')
	      return 0;
	    break;
	  case '\0':
	    return (*string == '\0');
	  default:
	    if (*pattern++ != *string++)
	      return 0;
	  }
	}
}

/*
 * This routine links a group of addresses (described by what vp points at)
 * into the Tholian Web (err, our matrix). The flag (either L_HOST or
 * L_CHANNEL) selects a namespace of strings pointed at by s. It just
 * happens we need 2 (host and channel names), and we don't care what
 * they are as long as they are in separate spaces.
 */
static void link_in(flag, vp, s)
	int flag;
	struct vertex *vp;
	const char *s;
{
	struct web *wp = web_findcreate(flag,s);

	wp->linkcnt += 1;

	vp->next[flag] = NULL;
	vp->prev[flag] = wp->lastlink;
	vp->orig[flag] = wp;
	if (wp->lastlink != NULL)
	  wp->lastlink->next[flag] = vp;
	wp->lastlink = vp;
	if (wp->link == NULL)
	  wp->link = vp;
}

/*
 * time-string to be prepended to logged messages
 */
char *
timestring()
{
	static char timebuf[40];
	struct tm *tp;

	mytime(&now);
	tp = localtime(&now);
	sprintf(timebuf,"%d%02d%02d%02d%02d%02d",
		tp->tm_year+1900, tp->tm_mon+1, tp->tm_mday,
		tp->tm_hour, tp->tm_min, tp->tm_sec);
	return timebuf;
}

static int running_on_alarm;
static time_t alarm_time;

static RETSIGTYPE sig_alarm(sig)
int sig;
{
	time(&alarm_time);
	SIGNAL_HANDLE(SIGALRM, sig_alarm);
	alarm(1);
}

static int    timeserver_pid = 0;

static void timer_health_check __((void))
{
  /* XXX: TODO! TIMER HEALTH CHECK */
  if (timeserver_pid > 0) {
  }
  if (running_on_alarm) {
  }
}


#if defined(HAVE_MMAP)

struct timeserver *timeserver_segment = NULL;
static void init_timeserver()
{
	int ppid;

	if ( Z_SHM_MIB_is_attached() ) {

	  timeserver_segment = & MIBMtaEntry->ts;

	} else { /* SHARED MIB MEMORY BLOCK IS NOT ATTACHED */

#define MAPSIZE 16*1024 /* Just in case other methods didn't work.. e.g.
			   that MIB-block.. */

#if !defined(MAP_ANONYMOUS) || defined(__linux__)
	  /* must have a file ? (SunOS 4.1, et.al.) */
	  int fd = -1;
	  char blk[1024];
	  int i;
	  Sfio_t *fp = sftmp(0); /* Create the backing file fairly reliably. */

	  if (fp)
	    fd = sffileno(fp);
	  if (fd < 0) {
	    perror("init_timeserver() didn't create tempfile ??");
	    return; /* Brr! */ 
	  }
	  
	  memset(blk,0,sizeof(blk));
	  for (i=0; i < MAPSIZE; i += sizeof(blk))
	    sfwrite(fp, blk, sizeof(blk));
	  sfsync(fp);
	  sfseek(fp, 0, 0);

#ifndef MAP_FILE
# define MAP_FILE 0 /* SunOS 4.1 does not have this */
#endif
	  timeserver_segment = (void*)mmap(NULL, MAPSIZE, PROT_READ|PROT_WRITE,
					   MAP_FILE|MAP_SHARED, fd, 0);
	  sfclose(fp);
	
#else /* MAP_ANONYMOUS and not Linux */

#ifndef MAP_VARIABLE
# define MAP_VARIABLE 0 /* Some system have MAP_ANONYMOUS, but
			   no MAP_VARIABLE.. */
#endif
	  /* This MAP_ANONYMOUS does work at DEC OSF/1 ... */
	  timeserver_segment = (void*)mmap(NULL, MAPSIZE, PROT_READ|PROT_WRITE,
					   MAP_VARIABLE|MAP_ANONYMOUS|MAP_SHARED,
					   -1, 0);
#endif
	  if (-1L == (long)timeserver_segment
	      || timeserver_segment == NULL) {
	    perror("mmap() of timeserver segment gave");
	    timeserver_segment = NULL;
	    return; /* Brr.. */
	  }

	} /* Have global shared server segment, or not ... */

	ppid = fork();
	if (ppid > 0) {
	  time_t now2;
	  timeserver_pid = ppid;
	  timeserver_segment->pid = ppid;

	  time(&now);
	  sleep(2);

#ifdef HAVE_SELECT
	  now2 = timeserver_segment->tv.tv_sec;
#else
	  now2 = timeserver_segment->time_sec;
#endif
	  if (now2 == 0 || now2 == now) {
	    /* HUH ?! No incrementation in 2 seconds ?? */
	    /* Start ticking in alarm() mode! */
	    kill (ppid, SIGTERM);
	    timeserver_pid = 0;
	    timeserver_segment = NULL;
	    alarm(1);
	  }

	  return;
	}

	if (ppid < 0) return; /* Error ?? brr.. */


	/* ========  TIME SERVER CHILD ======= */


	{

	  int space_check_count = 0;
	  char *p;

	  MIBMtaEntry->sc.schedulerTimeserverStartTime = time(NULL);
	  MIBMtaEntry->sc.schedulerTimeserverStarts ++;


	  close(0); close(1); close(2);
	  if (statuslog) sfclose(statuslog);

	  /* Create file handles (and temp files) for studying
	     file system (free) space state. */

	  p = malloc(strlen(TRANSPORTDIR)+50);
	  if (p) {
	    sprintf(p, "../%s/.%d.spacetest", QUEUEDIR, getpid());
	    QSpoolFd = open( p, O_RDWR|O_CREAT, 0600 );
	    unlink(p);unlink(p);
	    
	    sprintf(p, "../%s/.%d.spacetest", TRANSPORTDIR, getpid());
	    TSpoolFd = open( p, O_RDWR|O_CREAT, 0600 );
	    unlink(p);unlink(p);

	    free(p);
	  }


#ifdef HAVE_SETPROCTITLE
	  setproctitle("[TimeServer]");
#else
	  strncpy(ArgvSave,"[TimeServer]", EOArgvSave - ArgvSave);
#endif

	  if (ArgvSave < EOArgvSave)
	    ArgvSave[EOArgvSave-ArgvSave-1] = 0;

	  ppid = getppid(); /* who is our parent ? */

#ifdef HAVE_SELECT
	  gettimeofday((struct timeval *)&timeserver_segment->tv, NULL);
#else
	  time((time_t *)&timeserver_segment->time_sec);
#endif

	  for(;;) {
#ifdef HAVE_SELECT
	    struct timeval tv;
	    int rc;

	    tv.tv_sec = 0;
	    tv.tv_usec = 300000;

	    gettimeofday((struct timeval *)&timeserver_segment->tv, NULL);

	    rc = select(0,NULL,NULL,NULL,&tv);
#else
	    time((time_t *)&timeserver_segment->time_sec);
	    sleep(1); /* We don't have select() to use.. */
#endif
	    /* Is the parent still alive ?? */
	    if (kill(ppid, 0) != 0)
	      break; /* No ?? Out! */

	    /* Now check and fill in the filesystem free space
	       gauges */
	    if (--space_check_count  < 0) {

	      long bavail, bused, iavail, iused;
	      if (QSpoolFd >= 0 &&
		  ! fd_statfs(QSpoolFd, &bavail, &bused, &iavail, &iused)) {
		MIBMtaEntry->sys.SpoolUsedSpace = bused;
		MIBMtaEntry->sys.SpoolFreeSpace = bavail;
		MIBMtaEntry->sys.SpoolUsedFiles = iused;
		MIBMtaEntry->sys.SpoolFreeFiles = iavail;
	      }
	      if (TSpoolFd >= 0 &&
		  ! fd_statfs(TSpoolFd, &bavail, &bused, &iavail, &iused)) {
		MIBMtaEntry->sys.TportSpoolUsedSpace = bused;
		MIBMtaEntry->sys.TportSpoolFreeSpace = bavail;
		MIBMtaEntry->sys.TportSpoolUsedFiles = iused;
		MIBMtaEntry->sys.TportSpoolFreeFiles = iavail;
	      }

	      /* Log FS space is monitored by the self-timed
		 log reinit code. */

#ifdef HAVE_SELECT
	      space_check_count = 100; /* ticks about 3 times a second */
#else
	      space_check_count =  30; /* ticks once a second.. */
#endif
	    }

	  }

	} /* time-server child block */

	_exit(0);
}
#else
static void init_timeserver()
{
  /* Do nothing.. */
}

#endif

time_t mytime(timep)
time_t *timep;
{
	static int healthcheck = 10000;

	if (--healthcheck <= 0) {
	  healthcheck = 10000;
	  timer_health_check();
	}
#if defined(HAVE_MMAP)
	if (timeserver_pid) {
	  time_t t;
#ifdef HAVE_SELECT
	  t = timeserver_segment->tv.tv_sec;
#else
	  t = timeserver_segment->time_sec;
#endif
	  if (timep != NULL)
	    *timep = t;
	  return t;
	}
#endif
	if (running_on_alarm) {
	  if (timep)
	    *timep = alarm_time;
	  return alarm_time;
	}
#ifdef HAVE_GETTIMEOFDAY
	{
	  struct timeval tv;
	  gettimeofday(&tv,NULL);
	  if (timep)
	    *timep = tv.tv_sec;
	  return tv.tv_sec;
	}
#else
	return time(timep); /* The classical old version.. */
#endif
}

const char *
cfpdirname(hash)
int hash;
{
	static char dirbuf[8];

	if (hash < 0)
	  return "";
	if (hash < 256) {
	  sprintf(dirbuf, "%c/", hash);
	} else {
	  sprintf(dirbuf, "%c/%c/", (hash >> 8) & 0xff, hash & 0xff);
	}
	return dirbuf;
}


/* We make one, or at most two subdirs */

void
cfp_mksubdirs(topdir,newpath)
const char *topdir, *newpath;
{
	char path[256];
	int omask = umask(022);
	char *s;

	if (*topdir != 0)
	  sprintf(path, "../%s/%s", topdir, newpath);
	else
	  strcpy(path, newpath);

	s = strrchr(path,'/');
	if (s[1] == 0) *s = 0; /* Trailing slash elimination */

	if (mkdir(path,02755) != 0) {
	  char *s = strrchr(path,'/');
	  if (s) *s = 0;
	  mkdir(path,02755);
	  if (s) *s = '/';
	  mkdir(path,02755);
	}
	umask(omask);
}
