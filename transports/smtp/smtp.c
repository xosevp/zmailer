/*
 *	Copyright 1988 by Rayan S. Zachariassen, all rights reserved.
 *	This will be free software, but only when it is finished.
 *	Copyright 1991-2007 by Matti Aarnio -- modifications, including
 *	MIME things...
 */

#include "smtp.h"

/* About timeouts the RFC 1123 recommends:
     - Initial 220: 5 minutes
     - MAIL, RCPT : 5 minutes
     - DATA initialization (until "354.."): 2 minutes
     - While writing data, a block
       at the time: 3 minutes  (How large a block ?)
       (We increased this to 5 minutes)
     - From "." to "250 OK": 10 minutes
       (We use 20 minutes here - sendmail uses 60 minutes..)
 */
int timeout;			/* how long do we wait for response? (sec.) */
int timeout_cmd  =  5*60;
int timeout_data =  5*60;	/* in PIPELINING mode, 5 minutes is better! */
int timeout_tcpw =  5*60;	/* All tcp writes ?? */
int timeout_dot  = 20*60;
int timeout_conn =  3*60;	/* connect() timeout */

int sockwbufsize;

const char *defcharset;
char myhostname[512];
int myhostnameopt;
char errormsg[ZBUFSIZ]; /* Global for the use of  dnsgetrr.c */
const char *progname;
const char *cmdline, *eocmdline, *logfile, *msgfile;
int pid;
int debug;
int verbosity;
int conndebug;
int dotmode;			/* At the SMTP '.' phase, DON'T LEAVE IMMEDIATELY!. */
int getout;			/* signal handler turns this on when we are wanted to abort! */
int gotalarm;			/* indicate that alarm happened! */
jmp_buf procabortjmp;
int procabortset;
int readalready;		/* does buffer contain valid message data? */
int wantreserved;		/* open connection on secure (reserved) port */
int statusreport;		/* put status reports on the command line */
int force_8bit;			/* Claim to the remote to be 8-bit system, even
				   when it doesn't report itself as such..*/
int force_7bit;			/* and reverse the previous.. */
int keep_header8;		/* Don't do "MIME-2" to the headers */
int canon_mailfrom;		/* Set to do RFC-821/2821 MAIL FROM domain
				   canonication processing.  Usually only the
				   RCPT TO domains need to be canonicalized. */
int checkwks;
FILE *logfp;
extern int nobody;
char *localidentity;		/* If we are wanted to bind some altenate
				   interface than what the default is thru
				   normal kernel mechanisms.. */
int daemon_uid = -1;
int first_uid;			/* Make the opening connect with the UID of the
				   sender (atoi(rp->addr->misc)), unless it is
				   "nobody", in which case use "daemon"      */

int D_alloc;			/* Memory usage debug */
int no_pipelining;		/* In case the system just doesn't cope with it */
#if defined(AF_INET6) && defined(INET6)
int use_ipv6 = 1;
int prefer_ip6 = 1;
#endif
int close_after_data;

int lmtp_mode;			/* RFC 2033: LMTP mode */
int ignore_ezmlm;


#ifdef HAVE_OPENSSL
int demand_TLS_mode;		/* Demand TLS */
int tls_available;		/* local client code running ok */
char *tls_conf_file = NULL;
#endif /* - HAVE_OPENSSL */

const char *FAILED = "failed";
time_t now;

extern time_t retryat_time;	/* diagnostic() thing */

static void tcpstream_nagle   __((int fd));
static void tcpstream_denagle __((int fd));

char *authpasswdfile;


time_t starttime, endtime;


static const char *add_cname_cache __((SmtpState *SS, const char *host, const char *realname, time_t realnamettl));
static int  cname_lookup    __((SmtpState *SS, const char *host, const char ** cnamep));

static void SMTP_MIB_diag __((const int smtpstatus));


const char *
sysexitstr(r)
     int r;
{
  static char buf[20];
  switch (r) {
  case EX_OK:		return "OK";
  case EX_USAGE:	return "USAGE";
  case EX_DATAERR:	return "DATAERR";
  case EX_NOINPUT:	return "NOINPUT";
  case EX_NOUSER:	return "NOUSER";
  case EX_NOHOST:	return "NOHOST";
  case EX_UNAVAILABLE:	return "UNAVAILABLE";
  case EX_SOFTWARE:	return "SOFTWARE";
  case EX_OSERR:	return "OSERR";
  case EX_OSFILE:	return "OSFILE";
  case EX_CANTCREAT:	return "CANTCREAT";
  case EX_IOERR:	return "IOERR";
  case EX_TEMPFAIL:	return "TEMPFAIL";
  case EX_PROTOCOL:	return "PROTOCOL";
  case EX_NOPERM:	return "NOPERM";
#ifdef EX_CONFIG /* Not everywhere! */
  case EX_CONFIG:	return "CONFIG";
#endif
  default:
    sprintf(buf,"SYSEXIT%d",r);
    return buf;
  }
}

char *logtag()
{
	static char buf[30];
	static int logcnt = 0;
	static time_t logstart = 0;

	if (logstart == 0)  time( &logstart );


	/*
	  
	   The rewritten log tag is  sort(1):able  to separate sessions
	   from the file.

	*/

	time(&now);

	sprintf( buf, "%05d%04X-%04d-%04d",
		 pid,
		 ((int)logstart) & 0xFFFF,
		 logcnt,
		 (((int)(now - logstart)) % 10000) );

	++logcnt;
	if (logcnt > 9999) logcnt = 0;

	return buf;
}

/*
 *  ssfgets(bufpp, bufsizep, infilep, SS)
 *
 *  ALMOST like  fgets(),  but will do the smtp connection close
 *  after 3 minutes delay of sitting here..
 *
 */

static char * ssfgets __((char **, int*, int, SmtpState *));
static char *
ssfgets(bufp, bufsizp, infd, SS)
char **bufp;
int *bufsizp;
int infd;
SmtpState *SS;
{
	int rc, i, buflen, bufsiz;
	long tv;
	time_t tmout;
	char *s;
	static struct zmpollfd *fds = NULL;
	int fdscount;

	time(&now);

	
	tmout = now + 3*60;


	s = *bufp;
	buflen = 0;
	bufsiz = *bufsizp -3;

outbuf_fillup:
	while (SS->stdinsize > SS->stdincurs) {
	  if (SS->stdinbuf[SS->stdincurs] == '\n') {
	    *s++ = '\n';
	    ++buflen;
	    *s = 0;
	    SS->stdincurs += 1;
	    /* Move down the buffer contents (if any) */
	    if (SS->stdinsize > SS->stdincurs)
	      memcpy(SS->stdinbuf, SS->stdinbuf+SS->stdincurs,
		     (SS->stdinsize - SS->stdincurs));
	    SS->stdinsize -= SS->stdincurs;
	    SS->stdincurs  = 0;
	    return *bufp;
	  }
	  *s = SS->stdinbuf[SS->stdincurs];
	  SS->stdincurs += 1;
	  ++buflen, ++s;
	  if (buflen >= bufsiz) {
	    /* Grow space */
	    *bufsizp <<= 1;
	    bufsiz = *bufsizp;
	    *bufp = realloc(*bufp, bufsiz);
	    bufsiz -= 3;
	    if (!*bufp) return NULL; /* OUT OF MEMORY! */
	    s = *bufp + buflen;
	  }
	}
	/* Still here, and nothing to chew on ?  Buffer drained.. */
	SS->stdincurs = 0;
	SS->stdinsize = 0;


	while (!getout) {

	  time(&now);
	  if (now < tmout)
	    tv = tmout - now;
	  else
	    tv = 0;

	  fdscount = 0;
	  zmpoll_addfd(&fds, &fdscount, infd, -1, NULL);

	  rc = zmpoll(fds, fdscount, tv * 1000);
	  time(&now);

	  if (now >= tmout && SS->smtpfp && sffileno(SS->smtpfp) >= 0) {

	    /* Timed out, and have a writable SMTP connection active.. */
	    /* Lets write a NOOP there. */

	    /* We have here a VERY SHORT protocol timeout! */
	    timeout = 30;

	    if (statusreport)
	      report(SS,"#idle NOOP");

	    smtp_flush(SS); /* Flush in every case */
	    i = smtpwrite(SS, 0, "NOOP", 0, NULL);
	    SS->rcptstates = 0; /* ignore replies */
	    if (i != EX_OK && SS->smtpfp != NULL) {
	      /* No success ?  QUIT + close! (if haven't closed yet..) */
	      if (!getout)
		smtpwrite(SS, 0, "QUIT", -1, NULL);
	      smtpclose(SS, 0);
	    }
	  }
	  if (now >= tmout)
	    tmout = now + 3*60; /* Another 'keepalive' in 3 minutes */

	  if (rc == 1) { /* We have only ONE descriptor readable.. */
	    /* Got something to read on 'infd' (or EOF)
	       .. and we are non-blocking! */
	    int rdspace = sizeof(SS->stdinbuf) - SS->stdinsize;
	    fd_nonblockingmode(infd);
	    rc = read(infd, SS->stdinbuf + SS->stdinsize, rdspace);
	    fd_blockingmode(infd);

	    if (rc == 0) /* EOF! */
	      break;

	    if (rc > 0) { /* We have data! */
	      SS->stdinsize += rc;
	      goto outbuf_fillup;
	    }
#if 0
	    if (rc < 0) /* EINTR, et.al. */
	      continue;
#endif
	  }
	}

	if (s == *bufp)
	  return NULL; /* NOTHING received, gotten EOF! */
	return *bufp; /* Not EOF, got SOMETHING */
			  
}

void wantout_sig(sig)
int sig;
{
  getout = 1;
  SIGNAL_HANDLE(sig,wantout_sig);
  SIGNAL_RELEASE(sig);
  if (!dotmode && procabortset) /* Not within protected phase ? */
    longjmp(procabortjmp,1);
}


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
  fprintf(stderr,"# malloc (%u) returns %p @%p\n",
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
  fprintf(stderr,"# realloc (%p,%u) returns %p @%p\n", ptr, (unsigned int) size, result, CALLER);
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
  fprintf(stderr,"# memalign (%u,%u) returns %p @%p\n",
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
  fprintf(stderr,"# freed pointer %p @%p\n", ptr, CALLER);
  /* Restore our own hooks */
  __malloc_hook = my_malloc_hook;
  __free_hook = my_free_hook;
}
#endif

static char *filename;
static int   filenamesize;
static int task_count;

const char *punthost; /* Besided of value, is also used as GLOBAL
			 state variable! */

static int net_socks_open_cnt;

static void MIBcountCleanup __((void))
{
	MIBMtaEntry->tasmtp.TaProcCountG -= 1;
	/* That is UNSIGNED, thus.. */
	if (MIBMtaEntry->tasmtp.TaProcCountG > 99999U)
	  MIBMtaEntry->tasmtp.TaProcCountG = 0;

	/* Clean this counter, just in case it is non-zero... */
	MIBMtaEntry->tasmtp.SmtpConnectsCnt  -= net_socks_open_cnt;
}



int
main(argc, argv)
	int argc;
	char *argv[];
{
	volatile char *channel = NULL, *host = NULL;
	int i, fd, errflg, c;
	volatile int smtpstatus;
	volatile int need_host = 0;
	int skip_host = 0;
	volatile int idle;
	volatile int noMX = 0;
 	volatile int selfconnect = 1;
	SmtpState SS;
	struct ctldesc *dp;
#ifdef	BIND
	volatile int checkmx = 0; /* check all destination hosts for MXness */
#endif	/* BIND */
	RETSIGTYPE (*oldsig)__((int));
	volatile const char *smtphost = NULL;
	int one_per_connection = 0;

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

#if defined(HAVE_LOCALE_H) && defined(HAVE_SETLOCALE) && defined(LC_ALL)
	setlocale(LC_ALL, "C");
#endif

	/* This assignment MUST precede readzenv() ! */
	progname = strrchr(argv[0], '/');
	if (progname == NULL)
	  progname = argv[0];
	else
	  ++progname;

	if (getenv("ZCONFIG")) readzenv(getenv("ZCONFIG"));

	setvbuf(stdout, NULL, _IOFBF, 8096*4 /* 32k */);
	fd_blockingmode(FILENO(stdout)); /* Just to make sure.. */

	Z_SHM_MIB_Attach(1); /* we don't care if it succeeds or fails.. */

	MIBMtaEntry->tasmtp.TaProcessStarts += 1;
	MIBMtaEntry->tasmtp.TaProcCountG    += 1;

	atexit(MIBcountCleanup);


	pid = getpid();
	msgfile = "?";
	getout = 0;
	cmdline = &argv[0][0];
	eocmdline = cmdline;

	memset(&SS,0,sizeof(SS));
	SS.main_esmtp_on_banner = -1; /* Presume existing per spec */
	SS.servport      = -1;
	SS.smtp_bufsize  = 64*1024;
	SS.ehlo_sizeval  = -1;
	smtp_flush(&SS);

	for (i = 0; argv[i] != NULL; ++i)
	  eocmdline = strlen(argv[i])+ argv[i] + 1;
	/* Can overwrite also the environment strings.. */
	for (i = 0; environ[i] != NULL; ++i)
	  eocmdline = strlen(environ[i]) + environ[i] + 1;

	SIGNAL_HANDLESAVE(SIGINT, SIG_IGN, oldsig);
	if (oldsig != SIG_IGN)
	  SIGNAL_HANDLE(SIGINT, wantout_sig);
	SIGNAL_HANDLESAVE(SIGTERM, SIG_IGN, oldsig);
	if (oldsig != SIG_IGN)
	  SIGNAL_HANDLE(SIGTERM, wantout_sig);
	SIGNAL_HANDLESAVE(SIGQUIT, SIG_IGN, oldsig);
	if (oldsig != SIG_IGN)
	  SIGNAL_HANDLE(SIGQUIT, wantout_sig);
	SIGNAL_HANDLESAVE(SIGHUP, SIG_IGN, oldsig);
	if (oldsig != SIG_IGN)
	  SIGNAL_HANDLE(SIGHUP, wantout_sig);
	SIGNAL_IGNORE(SIGPIPE);
	timeout = timeout_cmd;

#if defined(AF_INET6) && defined(INET6)
	{
	  int sk = socket(AF_INET6, SOCK_STREAM, 0);
	  if (sk > 0) close(sk);
	  if (sk < 0)
	    use_ipv6 = 0; /* No go :-(  Can't create IPv6 socket */
	}
#endif
	
	errflg = 0;
	channel = CHANNEL;
	wantreserved = debug = statusreport = 0;
	logfile = NULL;
	myhostname[0] = '\0';
	myhostnameopt = 0;
	SS.remotemsg[0] = '\0';
	SS.remotehost[0] = '\0';
	while (1) {
	  c = getopt(argc, argv, "A:c:deh:l:p:rsvw:xXDEF:L:HMO:PS:T:VWZ:1678");
	  if (c == EOF)
	    break;
	  switch (c) {
	  case 'A':
	    authpasswdfile = strdup(optarg);
	    break;
	  case 'c':		/* specify channel scanned for */
	    channel = strdup(optarg);
	    break;
	  case 'd':		/* turn on debugging output */
	    ++debug;
	    break;
	  case 'e':		/* expensive MX checking for *all* addresses */
#ifdef	BIND
	    checkmx = 1;
#else  /* !BIND */
	    ++errflg;
	    fprintf(stderr, "%s: -e unavailable, no nameserver support!\n",
		    progname);
#endif /* BIND */
	    break;
	  case 'h':		/* my hostname */
	    strncpy(myhostname,optarg,sizeof(myhostname)-1);
	    myhostname[sizeof(myhostname)-1] = 0;
	    myhostnameopt = 1;
	    break;
	  case 'l':		/* log file */
	    logfile = strdup(optarg);
	    break;
	  case 'p':		/* server port */
	    SS.servport = atoi(optarg);
	    break;
	  case 'P':
	    no_pipelining = 1;	/* It doesn't handle it.. */
	    break;
	  case 'r':		/* use reserved port for SMTP connection */
	    wantreserved = 1;
	    break;
	  case 's':		/* report status to command line */
	    statusreport = 1;
	    break;
	  case 'X':		/* allow self connect for -x */
	    selfconnect = 1;
	    break;
	  case 'x':		/* don't use MX records lookups */
	    noMX = 1;
	    break;
	  case 'D':		/* only try connecting to remote host */
	    conndebug = 1;
	    break;
	  case 'E':		/* don't do EHLO, unless target system
				   has "ESMTP" on its banner */
	    SS.main_esmtp_on_banner = 0; /* Do test for it */
	    break;
	  case 'F':		/* Send all SMTP sessions to that host,
				   possibly set also '-x' to avoid MXes! */
	    punthost = strdup(optarg);
	    break;
	  case 'H':
	    keep_header8 = 1;
	    break;
	  case 'L':		/* Specify which local identity to use */
	    localidentity = strdup(optarg);
	    break;
	  case 'M':
	    lmtp_mode = 1;
	    break;
	  case 'T':		/* specify Timeout in seconds */
	    if (CISTREQN(optarg,"conn=",5)) {
	      timeout_conn = parse_interval(optarg+5,NULL);
	      if (timeout_conn < 10) {
		fprintf(stderr, "%s: bad tcp connection timeout: %s\n",
			argv[0], optarg+5);
		++errflg;
	      }
	      break;
	    } else if (CISTREQN(optarg,"data=",5)) {
	      timeout_data = parse_interval(optarg+5,NULL);
	      if (timeout_data < 10) {
		fprintf(stderr, "%s: bad data timeout: %s\n",
			argv[0], optarg+5);
		++errflg;
	      }
	      break;
	    } else if (CISTREQN(optarg,"dot=",4)) {
	      timeout_dot = parse_interval(optarg+4,NULL);
	      if (timeout_dot < 10) {
		fprintf(stderr, "%s: bad data-dot-reply timeout: %s\n",
			argv[0], optarg+4);
		++errflg;
	      }
	      break;
	    } else if (CISTREQN(optarg,"tcpw=",5)) {
	      timeout_tcpw = parse_interval(optarg+5,NULL);
	      if (timeout_tcpw < 10) {
		fprintf(stderr, "%s: bad tcp-write timeout: %s\n",
			argv[0], optarg+5);
		++errflg;
	      }
	      break;
	    } else if (CISTREQN(optarg,"cmd=",4)) {
	      timeout_cmd = parse_interval(optarg+4,NULL);
	      optarg += 4;
	    } else
	      timeout_cmd = parse_interval(optarg,NULL);
	    if (timeout_cmd < 5) {
	      fprintf(stderr, "%s: bad general cmd timeout: %s\n",
		      argv[0], optarg);
	      ++errflg;
	    }
	    break;
	  case 'O':
	    if (CISTREQ(optarg,"ignore-ezmlm")) {
	      ignore_ezmlm = 1;
	    } else {
	      ++errflg;
	    }
	    break;
	  case 'v':
	    ++verbosity;
	    break;
	  case 'V':
	    prversion("smtp");
	    exit(0);
	    break;
	  case 'w':
	    sockwbufsize = atoi(optarg);
	    break;
	  case 'W':		/* Enable RFC974 WKS checks */
	    checkwks = 1;
	    break;
	  case '1':
	    one_per_connection = 1;
	    break;
	  case '8':
	    force_8bit = 1;
	    force_7bit = 0;
	    break;
	  case '7':
	    if (force_7bit) /* Double-7 locks the ESMTP away, can
			       then be turned into 'force-8' mode
			       without ESMTP */
	      SS.main_esmtp_on_banner = -2;
	    ++force_7bit;
	    force_8bit = 0;
	    break;
	  case 'Z':  /* Dummy option to carry HUGE parameter string for
			the report system to make sense.. at OSF/1, at least */
	    break;
#if defined(AF_INET6) && defined(INET6)
	  case '6':
	    prefer_ip6 = !prefer_ip6;
	    break;
#endif
	  case 'S':
	    /* -S /path/to/SmtpSSL.conf */
#ifdef HAVE_OPENSSL
	    tls_conf_file = strdup(optarg);
#endif /* - HAVE_OPENSSL */
	    break;
	  default:
	    ++errflg;
	    break;
	  }
	}
	if (noMX != 0 && selfconnect != 0)
		noMX = -2;	/* -2 means allow self connect */


	time(&now);


	if (errflg || optind > argc) {
	  fprintf(stderr,
		  "Usage: %s [-8|-8H|-7][-e][-r][-x][-X][-E][-P][-W][-T timeout][-h myhostname][-l logfile][-p portnum][-c channel][-F forcedest][-L localidentity][-S /path/to/SmtpSSL.conf] [host]\n", argv[0]);
	  exit(EX_USAGE);
	}

	if (SS.servport < 0)
	  SS.servport = IPPORT_SMTP;

	if (lmtp_mode && SS.servport == 25 &&
	    (!punthost || !STREQN(punthost,"UNIX:/",6))) {
	  fprintf(stderr,
		  "%s: LMTP mode is not allowed without explicite port specifier with value other than 25, or -F to UNIX-socket..\n", argv[0]);
	  exit(EX_USAGE);
	}

	if (optind < argc) {
	  host = strdup(argv[optind]);
	  strncpy(SS.remotehost, (char*)host, sizeof(SS.remotehost));
	  SS.remotehost[sizeof(SS.remotehost)-1] = 0;
	} else
	  need_host = 1;

	if (myhostnameopt == 0) {
	  /* Default it only when not having an explicite value
	     in it..   James S MacKinnon <jmack@Phys.UAlberta.Ca> */
	  getmyhostname(myhostname, sizeof myhostname);
	}

	if (conndebug && !debug && host) {
	  SS.firstmx = 0;
	  smtpconn(&SS, (char*)host, noMX);
	  exit(0);
	}

	logfp = NULL;
	if (logfile != NULL) {
	  if ((fd = open(logfile, O_CREAT|O_APPEND|O_WRONLY, 0644)) < 0)
	    fprintf(stdout, "# %s: cannot open logfile \"%s\"!\n",
		    argv[0], logfile);
	  else
	    logfp = (FILE *)fdopen(fd, "a");
	}

	if (logfp)
	  setvbuf(logfp, NULL, _IOLBF, 0);

	getnobody();
	getdaemon();

	defcharset = getzenv("DEFCHARSET");
	if (!defcharset)
	  defcharset = DefCharset;

	/* We need this later on .. */
	zopenlog("smtp", LOG_PID, LOG_MAIL);
	notary_settaid("smtp",getpid());

	/* We defer opening a connection until we know there is work */

	smtpstatus = EX_OK;
	idle = 0;
	SS.stdinsize = 0;
	SS.stdincurs = 0;

	filenamesize = 80;
	filename = malloc(filenamesize);

#ifdef	BIND
	res_init();
#ifdef RES_USE_INET6
#if defined(AF_INET6) && defined(INET6)
	if (!use_ipv6)
	  _res.options &= ~RES_USE_INET6;
#else
	_res.options &= ~RES_USE_INET6;
#endif
#endif
#endif

	if (logfp) {
	  char *cp;
	  time( & now );

	  cp = (char *) rfc822date( & now );
	  if (cp) cp[strlen(cp)-1] = 0;
	  else cp = "??";

	  fprintf(logfp,"%s#\tStart time: %s\n", logtag(), cp);
	}


	while (!getout && !zmalloc_failure) {
	  /* Input:
	       spool/file/name [ \t host.info ] \n
	   */
	  char *s;

	  fd_blockingmode(FILENO(stdout));

	  fprintf(stdout, "#hungry\n");
	  fflush(stdout);

	  if (statusreport) {
	    if (idle)
	      report(&SS,"#idle");
	    else
	      report(&SS,"#hungry");
	  }

	  /* if (fgets(filename, sizeof(filename), stdin) == NULL) break; */
	  if (ssfgets(&filename, &filenamesize, FILENO(stdin), &SS) == NULL)
	    break;

	  ++task_count; /* Just a debug tool */

	  readalready = 0; /* internal body read buffer 'flush' */
	  idle = 0; skip_host = 0;
	  if (strchr(filename, '\n') == NULL) break; /* No ending '\n' !  Must
						    have been partial input! */
	  if (logfp)
	    fprintf(logfp,"%s#\tjobspec: %s",logtag(),filename);

	  if (STREQ(filename, "#idle\n")) {
	    idle = 1;
	    MIBMtaEntry->tasmtp.TaIdleStates += 1;
	    continue; /* XX: We can't stay idle for very long, but.. */
	  }
	  if (emptyline(filename, filenamesize))
	    break;

	  time(&now);

	  MIBMtaEntry->tasmtp.TaMessages += 1;

	  s = strchr(filename,'\t');
	  if (s != NULL) {
	    *s++ = 0;

	    if (host && CISTREQ((char*)host,s)) {

	      /* XXX: Behaviour with 'close_after_data' ??? */

	      if (now < retryat_time) {
		/* Same host, we don't touch on it for a while.. */
		/* sleep(2); */
		if (logfp && verbosity > 1) {
		  fprintf(logfp,"%s#\t(too soon trying to touch on host with 'retryat' diagnostic -- flushing job queue..host='%s')\n",logtag(),host);
		}
		++skip_host;
	      }
	    }

	    /* If different target host, close the old connection.
	       In theory we could use same host via MX, but...     */
	    if (host && !STREQ(s,(char*)host)) {
	      smtp_flush(&SS); /* Flush in every case */
	      if (SS.smtpfp) {
		if (!getout && !zmalloc_failure) {
		  SS.rcptstates = 0;
		  smtpstatus = smtpwrite(&SS, 0, "QUIT", -1, NULL);
		} else
		  smtpstatus = EX_OK;
		smtpclose(&SS, 0);
		notary_setwtt(NULL);
		notary_setwttip(NULL);
		if (logfp)
		  fprintf(logfp, "%s#\t(closed SMTP channel - new host)\n",
			  logtag());
		strncpy(SS.remotehost, (char*)host, sizeof(SS.remotehost));
		SS.remotehost[sizeof(SS.remotehost)-1] = 0;
		if (statusreport)
		  report(&SS, "NewDomain: %s", host);
	      }
	      close_after_data = 0;
	    }
	    if (host) free((void*)host);
	    host = strdup(s);
	  } else
	    if (need_host) {
	      fprintf(stdout,"# smtp needs defined host!\n");
	      fflush(stdout);
	      continue;
	    }

	  if (debug > 1) { /* "DBGdiag:"-output */
	    fprintf(stdout,"# (fdcnt=%d, file:%.200s, host:%.200s)\n", countfds(), filename, host);
	    fflush(stdout);
	  }

#ifdef	BIND

	  if (checkmx)
	    dp = ctlopen(filename, (char*)channel, (char*)host, &getout, rightmx, &SS);
	  else
#endif /* BIND */
	    dp = ctlopen(filename, (char*)channel, (char*)host, &getout, NULL, NULL);

	  SS.sel_channel = (const char *)channel;
	  SS.sel_host    = (const char *)host;

	  if (dp == NULL) {
	    fprintf(stdout,"#resync %.200s\n", filename);
	    fflush(stdout);
	    if (logfp)
	      fprintf(logfp, "%s#\tc='%s' h='%s' #resync %s\n", logtag(), channel, host, filename);
	    continue;
	  }

	  /* Copy the spoolid string pointer */
	  SS.taspoolid = dp->taspoolid;

	  time(&starttime);
	  notary_setxdelay(0);
	
	  if (punthost)
	    smtphost = punthost;
	  else
	    smtphost = host;

	  if (dp->verbose) {
	    if (SS.verboselog)
	      fclose(SS.verboselog);
	    SS.verboselog = (FILE *)fopen(dp->verbose,"a");
	    if (SS.verboselog)
	      setvbuf(SS.verboselog, NULL, _IONBF, 0);
	  }


#ifdef HAVE_OPENSSL
	  if (SS.verboselog && tls_conf_file)
	    fprintf(SS.verboselog, "# tls_conf_file='%s'\n", tls_conf_file);

	  if (tls_conf_file && !tls_available) {
	    /* -S /path/to/SmtpSSL.conf */

	    tls_available = (tls_init_clientengine(&SS, tls_conf_file) == 0);

	    if (SS.verboselog)
	      fprintf(SS.verboselog,
		      "# -S '%s' tls_init_client_engine() -> tls_available=%d\n",
		      tls_conf_file, tls_available);
#if 0
	    else
	      fprintf(stderr,
		      "# -S '%s' tls_init_client_engine() -> tls_available=%d\n",
		      tls_conf_file, tls_available);
#endif
	  }
#endif /* - HAVE_OPENSSL */


	  smtpstatus = process(&SS, (struct ctldesc *)dp, smtpstatus,
			       (char*)smtphost, noMX);

	  if (one_per_connection) {
	    if (SS.smtpfp)
	      smtp_flush(&SS); /* Flush in every case */
	    if (SS.smtpfp)
	      smtpstatus = smtpwrite(&SS, 0, "QUIT", -1, NULL);
	    if (SS.smtpfp) {
	      smtpclose(&SS, 0);
	      if (logfp)
		fprintf(logfp, "%s#\t(closed SMTP channel - final close)\n", logtag());
	    }
	  }

	  if (SS.verboselog)
	    fclose(SS.verboselog);
	  SS.verboselog = NULL;

	  ctlclose(dp);
	} /* while (!getout) ... */

	if (SS.smtpfp && !getout) {
	  smtp_flush(&SS); /* Flush in every case */
	  smtpstatus = smtpwrite(&SS, 0, "QUIT", -1, NULL);
	}

	/* Close the channel -- if it is open anymore .. */
	if (SS.smtpfp) {
	  smtpclose(&SS, 0);
	  if (logfp)
	    fprintf(logfp, "%s#\t(closed SMTP channel - final close)\n", logtag());
	}

	if (SS.verboselog != NULL)
	  fclose(SS.verboselog);
	SS.verboselog = NULL;
	if (logfp)
	  fclose(logfp);
	logfp = NULL;

	return 0;
}

int
process(SS, dp, smtpstatus, host, noMX)
	SmtpState *SS;
	struct ctldesc *dp;
	volatile int smtpstatus;
	const char *host;
	int noMX;
{
	if (setjmp(procabortjmp) == 0) {

	  struct rcpt *rp, *rphead;
	  int loggedid;

	  procabortset = 1;

	  smtpstatus = EX_OK; /* Hmm... */
	  loggedid = 0;

	  SS->firstmx = 0; /* If need be to connect to a new host,
			      because the socket is not on, we start
			      from the begin of the MX list */

	  *SS->remotemsg = 0;

	  for (rp = rphead = dp->recipients; rp != NULL; rp = rp->next) {

	    if (rp->next == NULL
		|| rp->addr->link   != rp->next->addr->link
		|| rp->newmsgheader != rp->next->newmsgheader) {

	      if (smtpstatus == EX_OK) {

		if (logfp && !loggedid) {
		  loggedid = 1;
		  fprintf(logfp, "%s#\t%s: %s\n", logtag(), dp->msgfile, dp->logident);
		}

		smtpstatus = deliver(SS, dp, rphead, rp->next, host, noMX);
		
		/* Report (and unlock) all those recipients which aren't
		   otherwise diagnosed.. */

		/* This "not otherwise reported" status is
		   ALWAYS EX_TEMPFAIL;
		   Anything else is incorrect when the recipient
		   has not been processed at all.   */
		smtpstatus = EX_TEMPFAIL;

		for (;rphead && rphead != rp->next; rphead = rphead->next) {
		  if (rphead->lockoffset) {

		    notaryreport(rphead->addr->user, FAILED, NULL, NULL);
		    diagnostic(SS->verboselog, rphead, smtpstatus,
			       smtpstatus == EX_TEMPFAIL ? 60 : 0,
			       "%s", SS->remotemsg);
		    SMTP_MIB_diag(smtpstatus);
		    if (logfp) {
		      fprintf(logfp, "%s#\t", logtag());
		      diagnostic(logfp, rphead, smtpstatus,
				 smtpstatus == EX_TEMPFAIL ? 60 : 0,
				 "%s", SS->remotemsg);
		    }
		  }
		}

		rphead = rp->next;

	      } else {

		time(&endtime);
		notary_setxdelay((int)(endtime-starttime));
		while (rphead != rp->next) {
		  /* SMTP open -- meaning (probably) that we got reject
		     from the remote server */
		  /* NOTARY: address / action / status / diagnostic */
		  if (rphead->lockoffset) {

		    notaryreport(rp->addr->user,FAILED,
				 "5.0.0 (Target status indeterminable)",
				 NULL);
		    diagnostic(SS->verboselog, rphead, EX_TEMPFAIL,
			       smtpstatus == EX_TEMPFAIL ? 60 : 0,
			       "%s", SS->remotemsg);
		    SMTP_MIB_diag(smtpstatus);
		    if (logfp) {
		      fprintf(logfp, "%s#\t", logtag());
		      diagnostic(logfp, rphead, EX_TEMPFAIL,
				 smtpstatus == EX_TEMPFAIL ? 60 : 0,
				 "%s", SS->remotemsg);
		    }
		  }

		  rphead = rphead->next;
		}
	      }
	    }
	  }

	} else {
	  /* processing fails entirely if PROCABORT is received */
	  smtpstatus = EX_UNAVAILABLE;
	  smtpclose(SS, 1);
	  if (logfp)
	    fprintf(logfp, "%s#\t(procabort executed)\n", logtag());
	}

	procabortset = 0;

	return smtpstatus;
}
/*
 * deliver - deliver the letter in to user's mail box.  Return
 *	     errors and requests for further processing in the structure
 */

int
deliver(SS, dp, startrp, endrp, host, noMX)
	SmtpState *SS;
	struct ctldesc *dp;
	struct rcpt *startrp, *endrp;
	const char *host;
	int noMX;
{
	struct rcpt *rp = NULL;
	int nrcpt, rcpt_cnt, size, tout, hdrsize;
	int content_kind = 0;
	CONVERTMODE convertmode;
	int ascii_clean = 0;
	struct stat stbuf;
	const char *cname, *u = NULL;
	char SMTPbuf[2000];
	char const * const  se = SMTPbuf + 800;
	/* char const * const se2 = SMTPbuf + sizeof(SMTPbuf)-40; */
	char *s;
	int conv_prohibit = check_conv_prohibit(startrp);
	int hdr_mime2 = 0;
	int pipelining = 0;
	time_t env_start, body_start, body_end;
	struct rcpt *more_rp = NULL;
	struct rcpt **more_rpp = NULL;
	char **chunkblkptr = NULL;
	char *chunkblk = NULL;
	int early_bdat_sync = 0;
	struct ct_data  *CT  = NULL;
	struct cte_data *CTE = NULL;
	char **hdr;
	int doing_reopen, did_open;
	int r, once;

	MIBMtaEntry->tasmtp.TaDeliveryStarts += 1;

	hdr = has_header(startrp,"Content-Type:");
	if (hdr)
	  CT = parse_content_type(*hdr);

	if (!CT && SS->verboselog)
	  fprintf(SS->verboselog, ".. No Content-Type: header parsed ??\n");
	else if (CT && SS->verboselog)
	  fprintf(SS->verboselog, " Content-Type: '%s'/'%s'; charset='%s'; boundary='%s'; name='%s'\n",
		  CT->basetype ? CT->basetype : "<NIL>",
		  CT->subtype  ? CT->subtype  : "<NIL>",
		  CT->charset  ? CT->charset  : "<NIL>",
		  CT->boundary ? CT->boundary : "<NIL>",
		  CT->name     ? CT->name     : "<NIL>");

	hdr = has_header(startrp,"Content-Transfer-Encoding:");
	if (hdr)
	  CTE = parse_content_encoding(*hdr);
	if (CT) {
	  if (CT->basetype == NULL ||
	      CT->subtype  == NULL ||
	      !CISTREQ(CT->basetype,"text") ||
	      !CISTREQ(CT->subtype,"plain"))

	    /* Not TEXT/PLAIN! */
	    conv_prohibit = -1;
	  /* We don't know how to convert anything BUT  TEXT/PLAIN :-(  */
	}

	doing_reopen = 0;
	r = EX_TEMPFAIL;

	once = 2;

 re_open:

	did_open = 0;

	if (!SS->smtpfp) {
	
	  int openstatus;

	  /* Make the opening connect with the UID of the
	     sender (atoi(startrp->addr->misc)), unless it is
	     "nobody", in which case use "daemon"      */
	  if ((first_uid = atoi(dp->senders->misc)) < 0 ||
	      first_uid == nobody)
	    first_uid = daemon_uid;

	  if (doing_reopen) SS->firstmx = 0;

	  smtp_flush(SS); /* Flush in every case */
	  SS->cmdstate = 0;

	  openstatus = smtpopen(SS, host, noMX);
	  if (openstatus != EX_OK) {

	    /* If we are doing reopen, and it fails, we report
	       just EX_TEMPFAIL, and bail out... */

	    if (doing_reopen) openstatus = EX_TEMPFAIL;

	    for ( rp = startrp; startrp != rp->next; startrp = startrp->next) {
	      if (startrp->lockoffset) {
		notaryreport(startrp->addr->user, FAILED, NULL, NULL);
		diagnostic(SS->verboselog, startrp, openstatus, 60, "%s", SS->remotemsg);
		SMTP_MIB_diag(openstatus);
		if (logfp) {
		  fprintf(logfp, "%s#\t", logtag());
		  diagnostic(logfp, startrp, openstatus, 60, "%s", SS->remotemsg);
		}
	      }
	    }
	    r = openstatus;
	    goto post_cleanup;
	  }
	  did_open = 1;
	}


	pipelining = ( SS->ehlo_capabilities & ESMTP_PIPELINING );

	if (no_pipelining) pipelining = 0;
	SS->pipelining = pipelining;

	if (pipelining && did_open)
	  MIBMtaEntry->tasmtp.SmtpPIPELINING ++;

	SS->chunking   = ( SS->ehlo_capabilities & ESMTP_CHUNKING );

	convertmode = _CONVERT_NONE;

	/* If the header says '8BIT' and ISO-8859-* something,
	   but body is plain 7-bit, turn it to '7BIT', and US-ASCII */
	/* Or if this is some more complicated type... */
	ascii_clean = check_7bit_cleanness(dp);

	if (conv_prohibit >= 0) {

	  /* Content-Transfer-Encoding: 8BIT ? */
	  content_kind = cte_check(startrp);

	  if (ascii_clean && content_kind == 8) {
	    if (downgrade_charset(startrp, SS->verboselog))
	      content_kind = 7;
	  }

	  if (conv_prohibit == 7)
	    SS->ehlo_capabilities &= ~ESMTP_8BITMIME;

	  if (force_7bit)	/* Mark off the 8BIT MIME capability.. */
	    SS->ehlo_capabilities &= ~ESMTP_8BITMIME;

	  switch (content_kind) {
	  case 0:		/* Not MIME */
	    if ((SS->ehlo_capabilities & ESMTP_8BITMIME) == 0 &&
		!ascii_clean && !force_8bit) {
	      convertmode = _CONVERT_UNKNOWN;
	      /* It is ASCII clean */
	      downgrade_headers(startrp, convertmode, SS->verboselog);
	    }
	    break;
	  case 2:		/* MIME, but no C-T-E: -> defaults to 7BIT */
	  case 1:		/* C-T-E: BASE64  ?? */
	  case 7:		/* C-T-E: 7BIT */
	    convertmode = _CONVERT_NONE;
	    break;
	  case 8:		/* C-T-E: 8BIT */
	    if ((force_7bit || (SS->ehlo_capabilities & ESMTP_8BITMIME)== 0) &&
		!ascii_clean && !force_8bit) {
	      convertmode = _CONVERT_QP;
	      if (!downgrade_headers(startrp, convertmode, SS->verboselog))
		convertmode = _CONVERT_NONE; /* Failed! */
	    }
	    break;
	  case 9:		/* C-T-E: Quoted-Printable */
	    if (force_8bit || (SS->ehlo_capabilities & ESMTP_8BITMIME)) {
	      /* Force(d) to decode Q-P while transfer.. */
	      convertmode = _CONVERT_8BIT;
	      /*  UPGRADE TO 8BIT !  */
	      if (!qp_to_8bit(startrp))
		convertmode = _CONVERT_NONE;
	      content_kind = 10;
	      ascii_clean = 0;
	    }
	    break;
	  default:
	    /* ???? This should NOT happen! */
	    break;
	  } /* switch().. */

	  hdr_mime2 = headers_need_mime2(startrp);
	  if (hdr_mime2 && !keep_header8) {
	    headers_to_mime2(startrp,defcharset,SS->verboselog);
         }

	} else if (conv_prohibit == -1) {

	  if (CT && CT->basetype &&
	      CISTREQ(CT->basetype,"multipart")) {

	    if ((force_7bit || (SS->ehlo_capabilities & ESMTP_8BITMIME)== 0) &&
		!ascii_clean) {
	      convertmode = _CONVERT_MULTIPARTQP;
	      if (SS->verboselog)
		fprintf(SS->verboselog, " MULTIPART message with 8-bit set content, AND  forced encoding downgrade or with ESMTP encoding downgrade\n");
	    }

	  }
	  
	} /* else -- "Content-Conversion: Prohibited" */

	notary_setcvtmode(convertmode);

	if (SS->ehlo_capabilities & ESMTP_SIZEOPT) {

	  /* We can do this SIZE option analysis without trying to
	     feed this in the MAIL command */

	  if (SS->ehlo_sizeval > 0 &&
	      startrp->desc->msgsizeestimate > SS->ehlo_sizeval) {

	    /* Reuse SMTPbuf for writing an error report
	       explaining things a bit.. */

	    sprintf(SMTPbuf, "smtp; 552 (Current message size %d exceeds limit given by the remote system: %d)",
		    (int)startrp->desc->msgsizeestimate,
		    (int)SS->ehlo_sizeval);

	    if (SS->verboselog)
	      fprintf(SS->verboselog, "%s\n", SMTPbuf+6);
	    
	    time(&endtime);
	    notary_setxdelay((int)(endtime-starttime));
	    for (rp = startrp; rp && rp != endrp; rp = rp->next)
	      if (rp->lockoffset) {
		/* NOTARY: address / action / status / diagnostic / wtt */
		notaryreport(rp->addr->user, FAILED,
			     "5.3.4 (Message size exceeds limit given by remote system)", SMTPbuf);
		diagnostic(SS->verboselog, rp, EX_UNAVAILABLE, 0, "\r\r%s", SMTPbuf+6);
		SMTP_MIB_diag(EX_UNAVAILABLE);
		if (logfp) {
		  fprintf(logfp, "%s#\t", logtag());
		  diagnostic(logfp, rp, EX_UNAVAILABLE, 0, "\r\r%s", SMTPbuf+6);
		}
	      }

	    r = EX_UNAVAILABLE;
	    goto post_cleanup;
	  }
	}

	r = EX_OK;

 more_recipients:;

	if (more_rp != NULL) {

	  startrp   = more_rp;
	  *more_rpp = more_rp;

	  more_rp  = NULL;
	  more_rpp = NULL;

	  once = 1;
	}

	/* Scan onwards over possibly processed instances */
	while (startrp  &&  startrp != endrp  &&  startrp->lockoffset == 0)
	  startrp = startrp->next;

	if (once < 1 /* No progress ? */
	    || getout
	    || startrp == NULL || startrp == endrp) {

	  if (SS->chunkbuf) free(SS->chunkbuf);
	  SS->chunkbuf = NULL;

	  goto post_cleanup;
	}

	--once;

	if (SS->smtpfp) {

	  if ((SS->lastactiontime + 20) < time(NULL))
	    SS->do_rset = 1; /* over 20 seconds since last
				transaction on this link ? */

	  /* SMTP is open, do we want to  RSET ? */
	  if (SS->do_rset) {

	    SS->rcptstates = 0;

	    if (statusreport)
	      report(SS,"RSET wait");

	    smtp_flush(SS); /* Flush in every case */

	    timeout = 30; /* very short */
	    r = smtpwrite(SS, 0, "RSET", 0, NULL);

	    if (statusreport)
	      report(SS,"RSET rc=%d",r);

	    if (r != EX_OK) {
	      smtpclose(SS,1);
	      r = EX_TEMPFAIL;
	      doing_reopen = 1;
	      goto re_open;
	    }
	    r = EX_TEMPFAIL;
	  }
	} else {

	  /* SMTP isn't open, we re-open.. */
	  r = EX_TEMPFAIL;
	  doing_reopen = 1;
	  goto re_open;

	}

	SS->rcptstates = 0;

	/* We are starting a new pipelined phase */
	smtp_flush(SS); /* Flush in every case */

	/* Store estimate on how large a file it is */
	if (fstat(dp->msgfd, &stbuf) >= 0)
	  size = stbuf.st_size - dp->msgbodyoffset;
	else
	  size = -1;
	SS->msize = size;

	SS->do_rset = 1; /* Unless completed successfully,
			    we must do RSET later... */

	MIBMtaEntry->tasmtp.SmtpMAIL ++;

	strcpy(SMTPbuf, "MAIL From:<");
	s = SMTPbuf + 11;

	if (!STREQ(startrp->addr->link->channel,"error")) {

	  /* Copy the (possibly quoted) local part */
	  int quote = 0;

	  u = startrp->addr->link->user;

	  for ( ; *u && (s < se); ++u) {
	    const char c = *u;
	    if (c == '\\') {
	      *s++ = c; ++u;
	      if (*u == 0) break;
	      *s++ = *u;
	      continue;
	    }
	    if (c == quote) /* 'c' is non-zero here */
	      quote = 0;
	    else if (c == '"')
	      quote = '"';
	    else if (!quote && (c == '@'))
	      break;
	    *s++ = c;
	  }

	  if (startrp->ezmlm && !ignore_ezmlm) {
	    /* The EZMLM mode appendix... */
	    const char *p = startrp->ezmlm;
	    while (*p && (s < se)) *s++ = *p++;
	    if (s < se) *s++ = '-';
	    /* Make 'em unique..  tag on the taspoolid. */
	    p = dp->taspoolid;
	    while (*p && (s < se)) *s++ = *p++;
	  }

	  /* Normal (tail) mode */

	  if (*u == '@') *s++ = *u++;

	  /* If there is a domain ? */
	  if (*u != 0) {
	    /* Now is the CNAME thingie to be rewritten ? */
	    if (canon_mailfrom) {
	      if ((cname_lookup(SS, u, & cname) > 0) && cname) {
		/* Rewrote the domain */
		u = cname;
	      }
	    }
	    /* Copy the domain (original/cname). */
	    while ((s < se) && *u) *s++ = *u++;
	  }
	  *s = 0;

	  u = NULL;

	} /* non-error source address mode */

	*s++ = '>';
	*s = 0;

	if (SS->ehlo_capabilities & ESMTP_8BITMIME) {
	  strcpy(s, " BODY=8BITMIME");
	  s += strlen(s);
	}

	/* Size estimate is calculated in the  ctlopen()  by
	   adding msg-body size to the largest known header size,
	   though excluding possible header and body rewrites.. */

	if (SS->ehlo_capabilities & ESMTP_SIZEOPT) {
	  sprintf(s, " SIZE=%ld", startrp->desc->msgsizeestimate);
	  s += strlen(s);
	  MIBMtaEntry->tasmtp.SmtpOPT_SIZE ++;
	}

	/* DSN parameters ... */
	if (SS->ehlo_capabilities & ESMTP_DSN) {
	  if (startrp->desc->envid != NULL) {
	    sprintf(s," ENVID=%.800s",startrp->desc->envid);
	    s += strlen(s);
	    MIBMtaEntry->tasmtp.SmtpOPT_ENVID ++;
	  }
	  if (startrp->desc->dsnretmode != NULL) {
	    sprintf(s, " RET=%.20s", startrp->desc->dsnretmode);
	    MIBMtaEntry->tasmtp.SmtpOPT_RET ++;
	  }
	}

	time(&env_start); /* Mark the timestamp */

	timeout = timeout_cmd;
	/* MAIL FROM:<...> -- pipelineable.. */
	r = smtpwrite(SS, 1, SMTPbuf, pipelining, NULL);

	if (!SS->smtpfp || sffileno(SS->smtpfp) < 0) r = EX_TEMPFAIL; /* ALWAYS! */

	if (r != EX_OK) {
	  /* If we err here, we probably are in SYNC mode... */
	  /* Uh ??  Many new sendmail's have a pathological error mode:
	        MAIL FROM...
		451 cannot preopen /etc/aliases.db
		  (wait a bit)
		250 ... Sender ok.
	     We try to accomodate that behaviour, and resync,
	     although treat it as temporary error -- 4xx series.  */
	  if (SS->smtpfp) {
	    sleep(10); /* After a sleep of 10 seconds, if we find that
			  we have some new input, do close the connection */
	    if (has_readable(SS->smtpfd)) {
	      SS->cmdstate = SMTPSTATE_RCPTTO; /* Well, sort of .. */
	      /* Drain the input, and then close the channel */
	      smtp_sync(SS, EX_OK, 0);
	      smtpclose(SS, 1);
	      if (logfp)
		fprintf(logfp, "%s#\t(closed SMTP channel - MAIL FROM:<> got two responses! [or EOF])\n", logtag());
	    }
	  }
	  time(&endtime);
	  notary_setxdelay((int)(endtime-starttime));
	  if (SS->smtpfp) {
	    if (pipelining)
	      r = smtp_sync(SS, r, 0); /* Collect reports in blocking mode */
#if 0
	  } else {
	    r = EX_TEMPFAIL; /* XXX: ??? */
#endif
	  }

	  if (!SS->smtpfp && once > 0) {
	    r = EX_TEMPFAIL;
	    doing_reopen = 1;
	    goto re_open;
	  }

	  SS->cmdstate     = SMTPSTATE_RCPTTO; /* 1 + MAILFROM.. */

	  /* Returning here EX_TEMPFAIL while smtpfp == NULL will do
	     quick retry!  DON'T diagnose those now! */

	  if (r != EX_TEMPFAIL && !SS->smtpfp) {
	    for (rp = startrp; rp && rp != endrp; rp = rp->next) {
	      /* NOTARY: address / action / status / diagnostic */
	      if (rp->lockoffset) {
		notaryreport(rp->addr->user, FAILED,
			     "5.5.0 (Undetermined protocol error)",NULL);
		diagnostic(SS->verboselog, rp, r, 0, "%s", SS->remotemsg);
		SMTP_MIB_diag(r);
		if (logfp) {
		  fprintf(logfp, "%s#\t", logtag());
		  diagnostic(logfp, rp, r, 0, "%s", SS->remotemsg);
		}
	      }
	    }
	  }

	  /* More recipients to send ? */
	  goto more_recipients;
	}

	nrcpt = 0;
	rcpt_cnt = 0;

	for (rp = startrp; rp && rp != endrp; rp = rp->next) {

	  if (!rp->lockoffset) continue; /* SKIP IT! */

	  /* Make sure the recipient diagnostics status at this
	     point is "OK". */
	  rp->status = EX_OK;

	  if (++rcpt_cnt >= SS->rcpt_limit) {
	    /* Limit Count full */
	    more_rp  = rp->next;
	    more_rpp = & rp->next;
	    rp->next = NULL;
	  }
	  if (rp->ezmlm && !ignore_ezmlm) {
	    /* THIS recipient is EZMLM one */
	    more_rp  = rp->next;
	    more_rpp = & rp->next;
	    rp->next = NULL;
	  }
	  if (!ignore_ezmlm && !rp->ezmlm && rp->next && rp->next->ezmlm) {
	    /* THIS recipient isn't EZMLM one, but NEXT one is! */
	    more_rp  = rp->next;
	    more_rpp = & rp->next;
	    rp->next = NULL;
	  }

	  SS->cmdstate = SMTPSTATE_RCPTTO;

	  {
	    int quote = 0;
	    u = rp->addr->user;

	    strcpy(SMTPbuf, "RCPT To:<");
	    s = SMTPbuf + 9;

	    /* Copy the (possibly quoted) local part */
	    quote = 0;
	    for ( ; *u && (s < se); ++u) {
	      const char c = *u;
	      if (c == '\\') {
		*s++ = c; ++u;
		if (*u == 0) break;
		*s++ = *u;
		continue;
	      }
	      if (c == quote) /* 'c' is non-zero here */
		quote = 0;
	      else if (c == '"')
		quote = '"';
	      else if (!quote && (c == '@'))
		break;
	      *s++ = c;
	    }

	    if ('@' == *u) { /* Has "@-full" address, can, perhaps, rewrite. */
	      *s++ = *u++;
	      if (*u != 0) {
		cname = NULL;
		if ((cname_lookup(SS, u, & cname) > 0) && cname) {
		  u = cname;
		}
		while (*u && (s < se)) *s++ = *u++;
	      }
	    }
	    *s++ = '>';
	    *s = 0;
	  }


	  if (SS->ehlo_capabilities & ESMTP_DSN) {

	    if (rp->notifyflgs) {
	      const char *t = "";
	      strcat(s, " NOTIFY=");
	      s += strlen(s);
	      if (rp->notifyflgs & _DSN_NOTIFY_NEVER) {
		strcat(s ,"NEVER");
	      }
	      if (rp->notifyflgs & _DSN_NOTIFY_SUCCESS) {
		strcat(s, "SUCCESS");
		t = ",";
	      }
	      if (rp->notifyflgs & _DSN_NOTIFY_FAILURE) {
		strcat(s, t);
		strcat(s, "FAILURE");
		t = ",";
	      }
	      if (rp->notifyflgs & _DSN_NOTIFY_DELAY) {
		strcat(s, t);
		strcat(s, "DELAY");
	      }
	    } else
	      strcat(s, " NOTIFY=FAILURE,DELAY"); /* Default value.. */

	    MIBMtaEntry->tasmtp.SmtpOPT_NOTIFY ++;
	    MIBMtaEntry->tasmtp.SmtpOPT_ORCPT  ++;


	    s += strlen(s);

	    if (rp->orcpt != NULL) {
	      sprintf(s, " ORCPT=%.800s", rp->orcpt);
	    } else {
	      const char *p = rp->addr->user;
	      strcpy(s, " ORCPT=rfc822;");
	      s += strlen(s);
	      while (*p) {
		const u_char c = *p++;
		if ('!' <= c && c <= '~' && c != '+' && c != '=')
		  *s++ = c;
		else {
		  sprintf(s,"+%02X",c);
		  s += 3;
		}
	      }
	      *s = 0;
	    }
	  }
	  
	  MIBMtaEntry->tasmtp.SmtpRCPT ++;

	  timeout = timeout_cmd;
	  /* RCPT To:<...> -- pipelineable */
	  r = smtpwrite(SS, 1, SMTPbuf, pipelining, rp);
	  if (r != EX_OK) {
	    if (!SS->smtpfp || sffileno(SS->smtpfp) < 0) r = EX_TEMPFAIL; /* ALWAYS! */
	    if (!pipelining) {
	      if (r == EX_TEMPFAIL)
		SS->rcptstates |= RCPTSTATE_400;
	      else
		SS->rcptstates |= RCPTSTATE_500;
	      rp->status = r;
	    }
	    time(&endtime);
	    notary_setxdelay((int)(endtime-starttime));
	    if (SS->smtpfp) {
	      if (pipelining)
		r = smtp_sync(SS, r, 0); /* Collect reports -- by blocking */
	    } else
	      r = EX_TEMPFAIL;

	    /* NOTARY: address / action / status / diagnostic / wtt */
	    notaryreport(rp->addr->user, FAILED, NULL, NULL);
	    diagnostic(SS->verboselog, rp, r, 0, "%s", SS->remotemsg);
	    SMTP_MIB_diag(r);
	    if (logfp) {
	      fprintf(logfp, "%s#\t", logtag());
	      diagnostic(logfp, rp, r, 0, "%s", SS->remotemsg);
	    }
	    if (!SS->smtpfp)
	      break;

	  } else { /* r == EX_OK */

	    if (!pipelining)
	      SS->rcptstates |= RCPTSTATE_OK;
	    nrcpt       += 1;
	    SS->rcptcnt += 1;
	    /* Actually we DO NOT KNOW under PIPELINING,
	       we will need to sync this later on.. */
	    rp->status = EX_OK;
	  }

	} /* ... for (rp = startrp; rp && rp != endrp; rp = rp->next) ... */


	if (nrcpt == 0) {
	  /* all the RCPT To addresses were rejected, so reset server */

	  SS->cmdstate     = SMTPSTATE_DATA; /* 1 + RCPTTO.. */


	  r = EX_UNAVAILABLE;
	  if (SS->rcptstates & RCPTSTATE_400)
	    /* The smtpfp != NULL -> no retry for these
	       recipients -- at least not right away! */
	    r = EX_TEMPFAIL; /* Even ONE temp failure -> total result
				   is then TEMPFAIL */

	  /* Next time around will need to do "RSET" before MAIL FROM */

	  /* EZMLM or some such thing runs with more recipients.. */
	  goto more_recipients;
	}

	if (!SS->smtpfp) {

	  r = EX_TEMPFAIL;  /* Doing quick retry on these rcpts! */
	  /* More recipients to send ? */
	  goto more_recipients;
	}

	chunkblkptr   = NULL;
	SS->chunksize = 0;
	SS->chunkbuf  = NULL;

#ifndef DO_CHUNKING
	SS->chunking = 0;
#endif

	SS->cmdstate = SMTPSTATE_DATA;

	SS->doing_chunking = 0;
	if (SS->chunking && startrp->desc->msgsizeestimate < CHUNK_MAX_SIZE) {
	  SS->doing_chunking = 1;

	  timeout = timeout_tcpw;

	  chunkblk = NULL;
	  chunkblkptr = & chunkblk;

	  /* We do surprising things here, we construct
	     at first the headers (and perhaps some of
	     the body) into a buffer, then write it out
	     in BDAT transaction. */

	  time(&endtime);
	  notary_setxdelay((int)(endtime-starttime));

	  /* Sometimes it MIGHT make sense to sync incoming
	     status data.    When and how ? */

	  if (!pipelining ||
	      (startrp->desc->msgsizeestimate >= CHUNK_MAX_SIZE))
	    early_bdat_sync = 1;

	  if (SS->smtpfp && early_bdat_sync) {
	    /* Now is time to do synchronization .. */
	    r = smtp_sync(SS, EX_OK, 0); /* Up & until "BDAT".. */
	  }

	  if (r != EX_OK) {
	    /* XX:
	       #error  Uncertain of what to do ...
	       ... reports were given at each recipient, and if all failed,
	       we failed too.. (there should not be any positive diagnostics
	       to report...)
	     */
	    for (rp = startrp; rp && rp != endrp; rp = rp->next) {
	      if (rp->lockoffset) {
		/* NOTARY: address / action / status / diagnostic / wtt */
		notaryreport(rp->addr->user,FAILED,NULL,NULL);
		if (rp->status == EX_OK) rp->status = r;
		diagnostic(SS->verboselog, rp, rp->status, 0, "%s", SS->remotemsg);
		SMTP_MIB_diag(rp->status);
		if (logfp) {
		  fprintf(logfp, "%s#\t", logtag());
		  diagnostic(logfp, rp, rp->status, 0, "%s", SS->remotemsg);
		}
	      }
	    }


	    /* More recipients to send ? */
	    goto more_recipients;
	  }

	  /* OK, we synced, lets continue with BDAT ...
	     The RFC 1830 speaks of more elaborate
	     pipelining with BDAT, but lets do this
	     with checkpoints at first */

	} else {

	  /* No CHUNKING here... do normal DATA-dot exchange */

	  /* In PIPELINING mode ...... send "DATA" and SYNC ! */
	  /* In non-pipelining mode .. send "DATA" and SYNC ! */

	  MIBMtaEntry->tasmtp.SmtpDATA ++;

	  timeout = timeout_data;
	  r = smtpwrite(SS, 1, "DATA", 0 /* SYNC! */, NULL);
	  timeout = timeout_tcpw;

	  if (r != EX_OK) {
	    if (SS->smtpfp &&
		(SS->rcptstates & DATASTATE_OK)) {
	      /* HUH!!!
		 MAIL FROM/RCPT TO ones have failed, but DATA has succeeded !!
		 This is SERIOUSLY weird, but some may work even that way.. */
	      smtpclose(SS,1);
	      if (logfp)
		fprintf(logfp, "%s#\t(closed SMTP channel - DATA ok, but MAIL FROM/RCPT TO failed!  rc=%d)\n", logtag(), rp ? rp->status : -999);
	      r = EX_TEMPFAIL;
	    }
	    if (SS->smtpfp &&
		(SS->rcptstates & RCPTSTATE_400) &&
		(SS->rcptstates & FROMSTATE_OK)) {
	      SS->rcptstates = 0;
	      smtp_flush(SS); /* Flush in every case */
	      smtpwrite(SS, 0, "QUIT", -1, NULL);
	      smtpclose(SS,1);
	      if (logfp)
		fprintf(logfp, "%s#\t(closed SMTP channel - tempfails for RCPTs; 'too many recipients per session' ??  rc=%d)\n", logtag(), rp ? rp->status : -999);
	      if (SS->verboselog)
		fprintf(SS->verboselog, "(closed SMTP channel - tempfails for RCPTs; 'too many recipients per session' ??  rc=%d)\n", rp ? rp->status : -999);

	      if (SS->rcptstates & RCPTSTATE_OK)
		retryat_time = 0;

	      close_after_data = 1;
	      r = EX_TEMPFAIL;
	    }


	    /* Next time around will need to do "RSET" before MAIL FROM */
	    /* XX: Set  r = EX_TEMPFAIL;  ??? */

	    if (SS->verboselog)
	      fprintf(SS->verboselog," .. timeout ? smtp_sync() rc = %d\n",r);

	    /* XX:
	       #error  Uncertain of what to do ...
	       ... reports were given at each recipient, and if all failed,
	       we failed too.. (there should not be any positive diagnostics
	       to report...)
	     */
	    for (rp = startrp; rp && rp != endrp; rp = rp->next)
	      if (rp->lockoffset) {
		/* NOTARY: address / action / status / diagnostic / wtt */
		notaryreport(rp->addr->user,FAILED,NULL,NULL);
		if (rp->status == EX_OK) rp->status = r;
		diagnostic(SS->verboselog, rp, rp->status, 0, "%s", SS->remotemsg);
		SMTP_MIB_diag(rp->status);
		if (logfp) {
		  fprintf(logfp, "%s#\t", logtag());
		  diagnostic(logfp, rp, rp->status, 0, "%s", SS->remotemsg);
		}
	      }

	    /* More recipients to send ? */
	    goto more_recipients;
	  }

	  timeout = timeout_dot;
	}
	/* Headers are 7-bit stuff -- says MIME specs */

	time(&body_start); /* "DATA" issued, and synced */


	if (SS->smtpfp) {
#ifdef HAVE_OPENSSL
	  if (!SS->TLS.sslmode)
#endif /* - HAVE_OPENSSL */
	    tcpstream_nagle(sffileno(SS->smtpfp));
	}

	header_received_for_clause(startrp, rcpt_cnt, SS->verboselog);

	SS->hsize = swriteheaders(startrp, SS->smtpfp, "\r\n",
				  convertmode, 0, chunkblkptr);

	if (SS->verboselog) {
	  char **hdrs = *(startrp->newmsgheader);
	  if (*(startrp->newmsgheadercvt) != NULL &&
	      convertmode != _CONVERT_NONE)
	    hdrs = *(startrp->newmsgheadercvt);
	  
	  fprintf(SS->verboselog,
		  "Written headers:  ContentKind=%d, CvtMode=%d, hsize=%d\n------\n",
		  content_kind, (int)convertmode, SS->hsize);
	  
	  if (chunkblkptr && SS->hsize > 0)
	    fwrite(*chunkblkptr, 1, SS->hsize, SS->verboselog);
	  else if (SS->hsize <= 0)
	    fprintf(SS->verboselog," ****** WRITE FAILURE ****\n");
	  else
	    for ( ; hdrs && *hdrs; ++hdrs)
	      fprintf(SS->verboselog,"%s\n",*hdrs);
	}

	if (SS->hsize >= 0 && chunkblk) {

	  chunkblk = realloc(chunkblk, SS->hsize+2);
	  if (chunkblk) {
	    memcpy(chunkblk + SS->hsize, "\r\n", 2);
	    SS->hsize += 2;
	  } else {
	    SS->hsize = -1;
	  }

	} else if (SS->hsize >= 0) {

	  if (!sferror(SS->smtpfp))
	    sfprintf(SS->smtpfp, "\r\n");

	  if (sferror(SS->smtpfp))
	    SS->hsize = -1;

	}

	if (chunkblk) {
	  SS->chunksize  = SS->hsize;
	  SS->chunkspace = SS->hsize;
	  SS->chunkbuf   = chunkblk;
	  chunkblk = NULL;
	}

	if (SS->hsize < 0) {
	  int r = EX_TEMPFAIL;
	  if (SS->smtpfp) tcpstream_denagle(sffileno(SS->smtpfp));
	  for (rp = startrp; rp != endrp; rp = rp->next)
	    if (rp->lockoffset) {
	      time(&endtime);
	      notary_setxdelay((int)(endtime-starttime));
	      /* NOTARY: address / action / status / diagnostic / wtt */
	      notaryreport(rp->addr->user,FAILED,
			   "5.4.2 (Message header write failure)",
			   /* XX: FIX THE STATUS? */
			   "smtp; 566 (Message header write failure)");
	      if (rp->status == EX_OK) rp->status = r;
	      diagnostic(SS->verboselog, rp, rp->status, 0, "%s", "header write error");
	      SMTP_MIB_diag(rp->status);
	      if (logfp) {
		fprintf(logfp, "%s#\t", logtag());
		diagnostic(logfp, rp, rp->status, 0, "%s", "header write error");
	      }
	    }
	  if (SS->verboselog)
	    fprintf(SS->verboselog,"Writing headers after DATA failed\n");

	  if (SS->smtpfp) {
	    smtpclose(SS, 1);
	    if (logfp)
	      fprintf(logfp, "%s#\t(closed SMTP channel - message header write failure, status=%d  msg='%s')\n", logtag(), rp ? rp->status : -999, SS->remotemsg);
	  }

	  if (SS->chunkbuf) free(SS->chunkbuf);
	  SS->chunkbuf = NULL;

	  /* More recipients to send ? */
	  goto more_recipients;
	}

	/* Add the header size to the initial body size */
	if (SS->msize >= 0)
	  SS->msize += SS->hsize;
	else
	  SS->msize -= SS->hsize-1;

	hdrsize = SS->hsize;

	/* Append the message body itself */

	r = appendlet(SS, dp, convertmode, CT);

	if (r != EX_OK) {
	  time(&endtime);
	  if (SS->smtpfp) tcpstream_denagle(sffileno(SS->smtpfp));
	  notary_setxdelay((int)(endtime-starttime));
	  for (rp = startrp; rp && rp != endrp; rp = rp->next)
	    if (rp->lockoffset) {
	      notaryreport(rp->addr->user, FAILED,
			   "5.4.2 (Message write timed out;2)",
			   "smtp; 566 (Message write timed out;2)"); /* XX: FIX THE STATUS? */
	      if (rp->status == EX_OK) rp->status = r;
	      diagnostic(SS->verboselog, rp, rp->status, 0, "%s", SS->remotemsg);
	      SMTP_MIB_diag(rp->status);
	      if (logfp) {
		fprintf(logfp, "%s#\t", logtag());
		diagnostic(logfp, rp, rp->status, 0, "%s", SS->remotemsg);
	      }
	    }
	  /* Diagnostics are done, protected (failure-)section ends! */
	  dotmode = 0;
	  /* The failure occurred during processing and was due to an I/O
	   * error.  The safe thing to do is to just abort processing.
	   * Don't send the dot! 2/June/94 edwin@cs.toronto.edu
	   */
	  if (SS->smtpfp) {
	    smtpclose(SS, 1);
	    if (logfp)
	      fprintf(logfp, "%s#\t(closed SMTP channel - appendlet() failure, status=%d  msg='%s')\n", logtag(), rp ? rp->status : -999, SS->remotemsg);
	  }

	  if (SS->chunkbuf) free(SS->chunkbuf);
	  SS->chunkbuf = NULL;

	  report(SS, "%s", SS->remotemsg);

	  r = EX_TEMPFAIL; /* ?? */

	  /* More recipients to send ? */
	  goto more_recipients;
	}



	/*
	 * This is the one place where we *have* to wait forever because
	 * there is no reliable way of aborting the transaction.
	 * Note that a good and useful approximation to "forever" is one day.
	 * Murphy's Law you know: Connections will hang even when they can't.
	 */
	/* RFC-1123 says: 10 minutes! */
	tout = timeout;
	timeout = timeout_dot;

	dotmode = 1;

	gotalarm = 0;

	SS->cmdstate = SMTPSTATE_DATADOT;


	if (lmtp_mode) SS->rcptstates = 0;

	if (SS->doing_chunking) { /* BDAT mode */

	  r = bdat_flush(SS, 1);

	} else { /* Ordinary DATA-dot mode */


	  /* Following the lead of sendmail, we separate
	     the DATA ending ".CRLF" 'line' into separately
	     pushed TCP frame.  That is apparently necessary
	     as the world is full of braindead firewalls
	     which change the ending CRLF.CRLF into something
	     else...  Cisco PIX seems to be the most common
	     culprit.. [mea] 2002-Jun-25

	     Of course this separation might not survive possible
	     packet retransmission, and nagle-re-merge... */

	  report(SS, "DATA-flush (wait)");
	  if (SS->smtpfp) sfsync(SS->smtpfp);
	  if (SS->smtpfp) tcpstream_denagle(sffileno(SS->smtpfp));


	  report(SS, "DATA-dot wait");
	  r = smtpwrite(SS, 1, ".", lmtp_mode, NULL);
	  if (!lmtp_mode)
	    report(SS, "DATA-dot; rc=%d", r);

	  /* Special case processing: If we are in LMTP's dot-of-DATA
	     phase, always use  smtp_sync()  to handle our diagnostics. */

	  if (lmtp_mode && r == EX_OK) {
	    report(SS, "DATA-dot; LMTP sync!");
	    r = smtp_sync(SS, EX_OK, 0); /* BLOCKING! */
	  }
	}

	timeout = tout;
	if (r != EX_OK) {
	  time(&endtime);
	  notary_setxdelay((int)(endtime-starttime));
	  for (rp = startrp; rp && rp != endrp; rp = rp->next)
	    if (rp->lockoffset) {
	      notaryreport(rp->addr->user, FAILED,
#if 1
			   NULL, NULL
#else
			   "5.4.2 (Message write failed; possibly remote rejected the message)",
			   "smtp; 566 (Message write failed; possibly remote rejected the message)"
#endif
			   );
	      /* If remote closed socket, don't diagnose here, diagnose
		 later.. (might also retry via other server!) */
	      if (rp->status == EX_OK) rp->status = r;
	      if (r != EX_TEMPFAIL) {
		diagnostic(SS->verboselog, rp, rp->status, 0, "%s", SS->remotemsg);
		SMTP_MIB_diag(rp->status);
		if (logfp) {
		  fprintf(logfp, "%s#\t", logtag());
		  diagnostic(logfp, rp, rp->status, 0, "%s", SS->remotemsg);
		}
	      }
	    }

	  report(SS, "Body done; %s", SS->remotemsg);

	  /* Diagnostics are done, protected (failure-)section ends! */
	  dotmode = 0;

	  if (SS->smtpfp && gotalarm) {
	    smtpclose(SS, 1);
	    if (logfp)
	      fprintf(logfp, "%s#\t(closed SMTP channel - smtpwrite('.') failure)\n", logtag());
	  }

	  if (SS->chunkbuf) free(SS->chunkbuf);
	  SS->chunkbuf = NULL;

	  /* More recipients to send ? */
	  goto more_recipients;
	}

	time(&body_end); /* body endtime */

	if (logfp != NULL) {
	  if (r != EX_OK)
	    fprintf(logfp, "%s#\t%s\n", logtag(), SS->remotemsg);
	  else
	    fprintf(logfp, "%s#\t%d bytes, %d in header, %d recipients, %d secs for envelope, %d secs for body xfer\n",
		    logtag(), SS->hsize, hdrsize, nrcpt,
		    (int)(body_start - env_start),
		    (int)(body_end   - body_start));
	}
	time(&endtime);
	notary_setxdelay((int)(endtime-starttime));

	/* r == EX_OK */

	for (rp = startrp; rp && rp != endrp; rp = rp->next) {
	  if (rp->lockoffset) {
	    char *reldel = "-";
	    /* Turn off the flag of NOTIFY=SUCCESS, we have handled
	       the burden to the next server ... */
	    if (SS->ehlo_capabilities & ESMTP_DSN)
	      rp->notifyflgs &= ~ _DSN_NOTIFY_SUCCESS;
	    /* Remote wasn't DSN speaker, and we have NOTIFY=SUCCESS,
	       then we say, we "relayed" the message */
	    if (rp->notifyflgs & _DSN_NOTIFY_SUCCESS)
	      reldel = "relayed";
	    rp->status = r;
	    notaryreport(rp->addr->user, reldel, NULL, NULL);
	    diagnostic(SS->verboselog, rp, rp->status, 0, "%s", SS->remotemsg);
	    SMTP_MIB_diag(rp->status);
	    if (logfp) {
	      fprintf(logfp, "%s#\t", logtag());
	      diagnostic(logfp, rp, rp->status, 0, "%s", SS->remotemsg);
	    }
	  }
	}

	/* Diagnostics are done, protected section ends! */
	dotmode = 0;

	if (SS->smtpfp &&
	    (SS->rcptstates & RCPTSTATE_400) &&
	    (SS->rcptstates & FROMSTATE_OK)) {
	  SS->rcptstates = 0;
	  smtpwrite(SS, 0, "QUIT", -1, NULL);
	  smtpclose(SS,1);
	  if (logfp)
	    fprintf(logfp, "%s#\t(closed SMTP channel - tempfails for RCPTs; 'too many recipients per session' ??  rc=%d)\n", logtag(), rp ? rp->status : -999);
	  if (SS->rcptstates & RCPTSTATE_OK)
	    retryat_time = 0;
	  close_after_data = 1;
	}
	if (SS->smtpfp && close_after_data) {
	  SS->rcptstates = 0;
	  smtpwrite(SS, 0, "QUIT", -1, NULL);
	  smtpclose(SS,1);
	  if (logfp)
	    fprintf(logfp, "%s#\t(closed SMTP channel - ``close_after_data'' mode)\n", logtag());
	  retryat_time = 0;
	}

	/* If all fine, all is fine...  No need to RSET afterwards. */
	SS->do_rset = 0;


	/* More recipients to send ? */
	goto more_recipients;

 post_cleanup:


	if (CT)  free_content_type(CT);
	if (CTE) free_content_encoding(CTE);
	return r;


}


int
ehlo_check(SS,buf)
SmtpState *SS;
const char *buf;
{
	char *r = strchr(buf,'\r');
	if (r != NULL) *r = 0;
	if (STREQ(buf,"8BITMIME")) {
	  SS->ehlo_capabilities |= ESMTP_8BITMIME;
	  MIBMtaEntry->tasmtp.EHLOcapability8BITMIME ++;
	} else if (STREQ(buf,"DSN")) {
	  SS->ehlo_capabilities |= ESMTP_DSN;
	  MIBMtaEntry->tasmtp.EHLOcapabilityDSN ++;
	} else if (STREQ(buf,"ENHANCEDSTATUSCODES")) {
	  SS->ehlo_capabilities |= ESMTP_ENHSTATUS;
	  MIBMtaEntry->tasmtp.EHLOcapabilityENHANCEDSTATUSCODES ++;
	} else if (STREQ(buf,"CHUNKING")) {
	  SS->ehlo_capabilities |= ESMTP_CHUNKING;
	  MIBMtaEntry->tasmtp.EHLOcapabilityCHUNKING ++;
	} else if (STREQ(buf,"PIPELINING")) {
	  SS->ehlo_capabilities |= ESMTP_PIPELINING;
	  MIBMtaEntry->tasmtp.EHLOcapabilityPIPELINING ++;
	} else if (STREQ(buf,"STARTTLS")) {
#ifdef HAVE_OPENSSL
	  SS->ehlo_capabilities |= ESMTP_STARTTLS;
#endif /* - HAVE_OPENSSL */
	  MIBMtaEntry->tasmtp.EHLOcapabilitySTARTTLS ++;
	} else if (STREQN(buf,"SIZE ",5) ||
		   STREQ (buf,"SIZE")   ) {
	  SS->ehlo_capabilities |= ESMTP_SIZEOPT;
	  SS->ehlo_sizeval = -1;
	  if (buf[4] == ' ')
	    sscanf(buf+5,"%ld",&SS->ehlo_sizeval);
	  MIBMtaEntry->tasmtp.EHLOcapabilitySIZE ++;
	} else if (STREQN(buf,"AUTH ",5) ||
		   STREQN(buf,"AUTH=",5)      ) {
	  SS->ehlo_capabilities |= ESMTP_AUTH;
	  MIBMtaEntry->tasmtp.EHLOcapabilityAUTH ++;
	} else if (STREQN(buf,"DELIVERBY ",10) ||
		   STREQ (buf,"DELIVERBY")    ) {
	  SS->ehlo_capabilities |= ESMTP_DELIVERBY;
	  SS->ehlo_deliverbyval = -1;
	  if (buf[9] == ' ')
	    sscanf(buf+10,"%ld;",&SS->ehlo_deliverbyval);
	  MIBMtaEntry->tasmtp.EHLOcapabilityDELIVERBY ++;
	} else if (STREQN(buf,"X-RCPTLIMIT ",12)) {
	  int nn = atoi(buf+12);
	  if (nn < 10)
	    nn = 10;
	  if (nn > 100000)
	    nn = 100000;
	  SS->rcpt_limit = nn;
	}
	return 0;
}

/* Flag that banner contained "ESMTP" (case insensitive) */
void
esmtp_banner_check(SS,str)
SmtpState *SS;
char *str;
{
	char *s = str;
	while (*s) {
	  while (*s && *s != 'e' && *s != 'E') ++s;
	  if (!s) return;
	  if (CISTREQN(s,"ESMTP",5)) {
	    SS->esmtp_on_banner = 1; /* Found it */
	    return;
	  }
	  ++s;
	}
}


int
smtpopen(SS, host, noMX)
	const char *host;
	SmtpState *SS;
	int noMX;
{
	int i;
	int retries = 0;
	char SMTPbuf[1000];

	if (debug && logfp)
	  fprintf(logfp, "%s#\tsmtpopen: connecting to %.200s\n", logtag(), host);

	smtp_flush(SS);

	do {

	  SS->esmtp_on_banner = SS->main_esmtp_on_banner; /* -1: presume it, 0: test for it */
	  SS->ehlo_capabilities = 0;
	  SS->ehlo_sizeval = 0;
	  SS->rcpt_limit = 100; /* Max number of recipients per message */

	  i = smtpconn(SS, host, noMX);
	  if (i != EX_OK)
	    continue;

	  SS->cmdstate = SMTPSTATE_HELO;

	  if (lmtp_mode || (SS->esmtp_on_banner > -2 && force_7bit < 2)) {
	    /* Either it is not tested, or it is explicitely
	       desired to be tested, and was found! */
	    if (SS->myhostname && !myhostnameopt)
	      sprintf(SMTPbuf, "EHLO %.200s", SS->myhostname);
	    else
	      sprintf(SMTPbuf, "EHLO %.200s", myhostname);

	    if (lmtp_mode) {
	      SMTPbuf[0] = 'L';
	      MIBMtaEntry->tasmtp.SmtpLHLO ++;
	    } else {
	      MIBMtaEntry->tasmtp.SmtpEHLO ++;
	    }

	    i = smtp_ehlo(SS, SMTPbuf);

	    if (i == EX_OK) {
	      if (lmtp_mode)
		MIBMtaEntry->tasmtp.SmtpLHLOok ++;
	      else
		MIBMtaEntry->tasmtp.SmtpEHLOok ++;
	    } else {
	      if (lmtp_mode)
		MIBMtaEntry->tasmtp.SmtpLHLOfail ++;
	      else
		MIBMtaEntry->tasmtp.SmtpEHLOfail ++;
	    }


#ifdef HAVE_OPENSSL

	    if (logfp)
	      fprintf(logfp, "%s#\tEHLO rc=%d demand_TLS_mode=%d tls_available=%d%s %sPIPELINING\n", logtag(), i, demand_TLS_mode, tls_available, (SS->ehlo_capabilities & ESMTP_STARTTLS) ? " STARTTLS":"", (SS->ehlo_capabilities & ESMTP_PIPELINING) ? "":"no ");
	    if (SS->verboselog)
	      fprintf(SS->verboselog, "--> EHLO rc=%d demand_TLS_mode=%d tls_available=%d%s %sPIPELINING\n", i, demand_TLS_mode, tls_available, (SS->ehlo_capabilities & ESMTP_STARTTLS) ? " STARTTLS":"", (SS->ehlo_capabilities & ESMTP_PIPELINING) ? "":"no ");

	    if ((i == EX_OK) && demand_TLS_mode && tls_available &&
		!(SS->ehlo_capabilities & ESMTP_STARTTLS)) {

	      /* Whoops! No TLS at the server, while we are configured
		 to demand it! */

	      i = EX_UNAVAILABLE;
	      notaryreport(NULL,NULL,"5.7.3 (Mandated TLS security mode not available)",
			   "local; 500 (Remote system doesn't support mandated TLS mode)");
	      strcpy(SS->remotemsg,"500 (Remote system doesn't support mandated TLS mode)");

	      if (lmtp_mode) /* really sort of TLS failure... */
		MIBMtaEntry->tasmtp.SmtpLHLOfail ++;
	      else
		MIBMtaEntry->tasmtp.SmtpEHLOfail ++;

	      continue;
	    }

	    if ((i == EX_OK) && tls_available &&
		(SS->ehlo_capabilities & ESMTP_STARTTLS)) {

	      MIBMtaEntry->tasmtp.SmtpSTARTTLS += 1;

	      SS->rcptstates = 0;
	      timeout = timeout_cmd;
	      i = smtpwrite(SS, 0, "STARTTLS", 0, NULL);
	      if (i == EX_OK) {
		/* Wow, "STARTTLS" command started successfully! */
		i = tls_start_clienttls(SS, host);
		if (i)
		  MIBMtaEntry->tasmtp.SmtpSTARTTLSfail += 1;
		else
		  MIBMtaEntry->tasmtp.SmtpSTARTTLSok += 1;

		if (i != 0) {
		  /* TLS startup failed :-( */
		  smtpclose(SS, 1);

		  /* Only if we are configured to *demand* the TLS mode,
		     then this situation is an error! */

		  if (1 /* demand_TLS_mode */) {
		    i = EX_TEMPFAIL;
		    notaryreport(NULL,NULL,"5.7.3 (Mandated TLS security mode not available)",
				 "local; 500 (Remote system doesn't support mandated TLS mode)");
		    strcpy(SS->remotemsg,"500 (Remote system doesn't support mandated TLS mode)");
		    
		    continue;
		  }
		  /* Well, TLS startup failed, then just reopen same
		     server, and don't redo  STARTTLS. */
		}

#if 0
		/*
		 * Now the connection is established and maybe we
		 * do have a validated cert with a CommonName in it.
		 * In enforce_peername state, the handshake would
		 * already have been terminated so the check here
		 * is for logging only!
		 */
		if (session->tls_info.peer_CN) {
		  if (!session->tls_info.peer_verified) {
		    msg_info("Peer certficate could not be verified");
		    if (session->tls_enforce_tls) {
		      pfixtls_stop_clienttls(session->stream,
					     var_smtp_starttls_tmout, 1,
					     &(session->tls_info));
		      return(smtp_site_fail(state, 450, "TLS-failure: Could not verify certificate"));
		    }
		  }
		} else if (session->tls_enforce_tls) {
		  pfixtls_stop_clienttls(session->stream,
					 var_smtp_starttls_tmout, 1,
					 &(session->tls_info));
		  return (smtp_site_fail(state, 450, "TLS-failure: Cannot verify hostname"));
		}
#endif
		if (SS->verboselog) {
		  if (i == EX_OK) {
		    fprintf(SS->verboselog,
			    " TLS mode running successfully!\n");
		    if (SS->TLS.cipher_name)
		      fprintf(SS->verboselog,
			      " TLS cipher: %s\n", SS->TLS.cipher_name);
		    if (SS->TLS.protocol)
		      fprintf(SS->verboselog,
			      " TLS protocol: %s\n", SS->TLS.protocol);
		    fprintf(SS->verboselog,
			    " TLS cipher bits: %d in use: %d\n",
			    SS->TLS.cipher_algbits, SS->TLS.cipher_usebits);
		    fprintf(SS->verboselog,
			    " TLS peer CN-1:             %s\n",
			    SS->TLS.peer_CN1 ? SS->TLS.peer_CN1 : "<>");
		    fprintf(SS->verboselog,
			    " TLS peer cert issuer name: %s\n",
			    SS->TLS.issuer_CN1 ? SS->TLS.issuer_CN1 : "<>");
		    fprintf(SS->verboselog,
			    " Cert not valid Before:     %s\n",
			    SS->TLS.notBefore ? SS->TLS.notBefore : "<>");
		    fprintf(SS->verboselog,
			    " Cert not valid After:      %s\n",
			    SS->TLS.notAfter ? SS->TLS.notAfter : "<>");
		  } else
		    fprintf(SS->verboselog, " Failed the TLS startup!\n");
		}

		/* Now re-negotiate the modes, possibly after
		   reopening the connection.  */

		SS->ehlo_capabilities = 0;
		SS->ehlo_sizeval = 0;
		SS->rcpt_limit = 100; /* Max number of recipients per msg */

		if (i != EX_OK) {
		  SS->esmtp_on_banner = SS->main_esmtp_on_banner;
		  i = makereconn(SS);
		} else
		  i = EX_OK; /* Even if 'EX_OK' is zero.. */

		if (i != EX_OK)
		  continue;

	      } else {
		smtpclose(SS, 1); /* D'uh.. STARTTLS verb failed! */
		
		MIBMtaEntry->tasmtp.SmtpSTARTTLSfail += 1;

		SS->esmtp_on_banner = SS->main_esmtp_on_banner;
		SS->ehlo_capabilities = 0;
		SS->ehlo_sizeval = 0;
		SS->rcpt_limit = 100; /* Max number of recipients per msg */

		i = makereconn(SS);
		if (i != EX_OK)
		  continue;
	      }
	      /* The system *did* successfully respond to EHLO previously,
		 why would it not do so now ??? */
	      i = smtp_ehlo(SS, SMTPbuf);
	      /* ... like for connection failing ... */
	    }
#endif /* - HAVE_OPENSSL */
	    if (i == EX_TEMPFAIL && !lmtp_mode) {
	      /* There are systems, which hang up on us, when we
		 greet them with an "EHLO".. Do here a normal "HELO".. */
	      i = makereconn(SS);
	      if (i != EX_OK)
		continue;
	      i = EX_TEMPFAIL;
	    }
	  } /* END "EHLO" connection */


	  /* If the remote has AUTH-capability, and we have
	     'authpasswdfile' set, call  smtpauth() !  */

	  if (authpasswdfile) {
	    if (SS->verboselog)
	      fprintf(SS->verboselog, " AUTHSECRETS file exists, EHLO rc=%d capa has AUTH: %d\n",
		      i, (SS->ehlo_capabilities & ESMTP_AUTH) != 0);
	  }

	  if ( (i == EX_OK) && (SS->ehlo_capabilities & ESMTP_AUTH) &&
	       authpasswdfile )
	    i = smtpauth(SS);


	  if (SS->esmtp_on_banner > -2 && i == EX_OK ) {
	    if (SS->verboselog)
	      fprintf(SS->verboselog,
		      "  EHLO response flags = 0x%02x, rcptlimit=%d, sizeopt=%ld\n",
		      (int)SS->ehlo_capabilities, (int)SS->rcpt_limit,
		      (long)SS->ehlo_sizeval);
	  } else if (!lmtp_mode) {
	    if (SS->myhostname && !myhostnameopt)
	      sprintf(SMTPbuf, "HELO %.200s", SS->myhostname);
	    else
	      sprintf(SMTPbuf, "HELO %.200s", myhostname);
	    MIBMtaEntry->tasmtp.SmtpHELO ++;

	    i = smtp_ehlo(SS, SMTPbuf);

	    if (i == EX_OK)
	      MIBMtaEntry->tasmtp.SmtpHELOok ++;
	    else
	      MIBMtaEntry->tasmtp.SmtpHELOfail ++;

	    if (i != EX_OK && SS->smtpfp) {
	      smtpclose(SS, 1);
	      if (logfp)
		fprintf(logfp, "%s#\t(closed SMTP channel - HELO failed ?)\n", logtag());
	    }
	    if (i == EX_TEMPFAIL || !SS->smtpfp || sffileno(SS->smtpfp) < 0) {
	      /* Ok, sometimes EHLO+HELO cause crash, open and do HELO only */
	      if (SS->smtpfp) smtpclose(SS, 1);
	      i = makereconn(SS);
	      if (i != EX_OK)
		continue;;
	      SS->rcptstates = 0;
	      timeout = timeout_cmd;
	      i = smtpwrite(SS, 1, SMTPbuf, 0, NULL);
	      if (i != EX_OK && SS->smtpfp) {
		smtpclose(SS, 1);
		if (logfp)
		  fprintf(logfp,
			  "%s#\t(closed SMTP channel - HELO failed(2))\n",
			  logtag());
	      }
	    }
	  }

	  ++retries;

	  if (SS->verboselog)
	    fprintf(SS->verboselog," retries=%d firstmx=%d mxcount=%d\n",
		    retries, SS->firstmx, SS->mxcount);

	} while ((i == EX_TEMPFAIL) && (SS->firstmx < SS->mxcount));

	if (logfp)
	  fprintf(logfp, "%s#\tsmtpopen: status = %d\n", logtag(), i);

	if (SS->verboselog)
	  fprintf(SS->verboselog, "smtpopen: result code %d / %s; socket is %sopen\n",
		  i, sysexitstr(i), SS->smtpfp ? "" : "not ");

	return i;
}

int
smtpconn(SS, host, noMX)
	SmtpState *SS;
	const char *host;
	int noMX;
{
	int	i, r, retval;
	char	hbuf[MAXHOSTNAMELEN+1];
	char    realname[1024];
	volatile int	rc;
	time_t  realnamettl;

	SS->literalport = -1;

	if (SS->firstmx == 0) {
	  SS->mxcount = 0;
	  /* Cleanup of the MXH array */
	  for (i = 0; i < MAXFORWARDERS; ++i) {
	    if (SS->mxh[i].host != NULL)
	      free(SS->mxh[i].host); /* memset() below clears these pointers */
	    if (SS->mxh[i].ai != NULL)
	      freeaddrinfo(SS->mxh[i].ai);
	  }
	  if (SS->verboselog)
	    fprintf(SS->verboselog, "memset(SS->mxh, 0, %d)\n",(int)sizeof(SS->mxh));
	  memset(SS->mxh, 0, sizeof(SS->mxh));
	}

#ifdef	BIND
	h_errno = 0;
#endif	/* BIND */

	stashmyaddresses(NULL);

	if (debug && logfp)
	  fprintf(logfp, "%s#\tsmtpconn: host = %.200s\n", logtag(), host);

	if (host[0] == '"' && host[1] == '[')
	  ++host;

#ifndef AF_UNIX
# ifdef AF_LOCAL
#  define AF_UNIX AF_LOCAL
# endif
#endif
#ifdef AF_UNIX
	if (punthost && STREQN(host,"UNIX:/",6)) {

	  /* We are going into a UNIX domain socket...
	     ... and this socket is defined at our command line!  */
	  
	  struct addrinfo *ai;
	  struct sockaddr_un *su;

	  su = malloc(256+8);
	  ai = malloc(sizeof(*ai));

	  if (ai && su) {

	    memset(ai, 0, sizeof(*ai));
	    memset(su, 0, 256+8);

	    ai->ai_next     = NULL;
	    ai->ai_family   = AF_UNIX;
	    ai->ai_socktype = SOCK_STREAM;
	    ai->ai_protocol = 0;
	    ai->ai_flags    = 0;
	    ai->ai_addr     = (void *) su;

	    su->sun_family = AF_UNIX;
#if HAVE_SA_LEN
	    su->sun_len = sizeof(su);
#endif
	    strncpy(su->sun_path, host+5, 256);
	    su->sun_path[255] = 0;

	    SS->mxcount = 0;
	    retval = makeconn(SS, host, ai, -2);

	  } else
	    retval = EX_TEMPFAIL; /* Out of memory... */

	  if (ai) free(ai);
	  if (su) free(su);

	  goto bail_out;

	}
#endif
	if (*host == '[') {	/* hostname is IP address literal */

	  char *cp, buf[500];
	  const char *hcp;
	  struct addrinfo req, *ai;

	  memset(&req, 0, sizeof(req));
	  req.ai_family   = 0; /* Either IPv4 or IPv6 ok */
	  req.ai_socktype = SOCK_STREAM;
	  req.ai_protocol = IPPROTO_TCP;
	  req.ai_flags    = AI_CANONNAME;
	  ai = NULL;

	  if (SS->verboselog)
	    fprintf(SS->verboselog,"SMTP: Connecting to host: %.200s (IP literal)\n",host);

	  for (cp = buf, hcp = host+1 ;
	       *hcp != 0 && *hcp != ']' && cp < (buf+500-1) ;
	       ++cp, ++hcp)
	    *cp = *hcp;
	  *cp = '\0';

	  if (*hcp == ']' &&
	      *++hcp == ':') {
	    ++hcp;
	    sscanf(hcp,"%d",&SS->literalport);
	  }

#if defined(AF_INET6) && defined(INET6)
	  if (CISTREQN(buf,"IPv6 ",5)  ||
	      CISTREQN(buf,"IPv6.",5)  ||
	      CISTREQN(buf,"IPv6:",5)  ) {
	    /* We parse ONLY IPv6 form of address .. well, also
	       the potential IPv4 compability addresses ... */
	    req.ai_family = PF_INET6;
#ifdef HAVE_GETADDRINFO
	    rc = getaddrinfo(buf+5, "0", &req, &ai);
#else
	    rc = _getaddrinfo_(buf+5, "0", &req, &ai, SS->verboselog);
#endif
	    if (SS->verboselog)
	      fprintf(SS->verboselog,
		      "getaddrinfo(INET6,'%s') -> r=%d, ai=%p\n",buf+5,rc,ai);
	  } else
#endif
	    {
	      /* Definitely only IPv4 address ... */
	      req.ai_family = PF_INET;
#ifdef HAVE_GETADDRINFO
	      rc = getaddrinfo(buf, "0", &req, &ai);
#else
	      rc = _getaddrinfo_(buf, "0", &req, &ai, SS->verboselog);
#endif
	      if (SS->verboselog)
		fprintf(SS->verboselog,
			"getaddrinfo(INET,'%s') -> r=%d, ai=%p\n",buf,rc,ai);
	    }
	  {
	    char nbuf[100];
	    sprintf(nbuf,"X-IP-addr; [%.80s]", buf);
	    notary_setwtt(nbuf);
	  }


	  if (rc != 0) {
	    sprintf(SS->remotemsg, "smtp; 500 (bad IP address: %.500s)", host);
	    time(&endtime);
	    notary_setxdelay((int)(endtime-starttime));
	    notaryreport(NULL,FAILED,"5.1.2 (bad literal IP address)",
			 SS->remotemsg);
	    if (SS->verboselog)
	      fprintf(SS->verboselog,"%s\n", SS->remotemsg+6);
	    if (ai != NULL)
	      freeaddrinfo(ai);
	    return EX_NOHOST;
	  }

	  SS->mxcount = 0;
	  retval = makeconn(SS, host, ai, -2);

	  goto bail_out;

	}

	/* Final "else" branch ... */
	if (1) {
	  /* HOSTNAME; (non-literal) */

	  if (SS->verboselog)
	    fprintf(SS->verboselog,"SMTP: Connecting to host: %.200s firstmx=%d mxcount=? noMX=%d\n",host,SS->firstmx, noMX);
	  hbuf[0] = '\0';
	  errno = 0;

	  /* use the hostent we got */
#ifdef	BIND
	  /*
	   * Look for MX RR's. If none found, use the hostentry in hp.
	   * Otherwise loop through all the mxhosts doing gethostbyname's.
	   */
	  if (!noMX && SS->firstmx == 0) {
	    if (SS->verboselog)
	      fprintf(SS->verboselog," getmxrr(%.200s)",host);

	    /*	We pick (dynamically!) our current interfaces,
		and thus can (hopefully!) avoid sending mail to
		ourselves thru MX pointed identity we didn't
		realize being ours!				*/
	    stashmyaddresses(NULL);

	    if (statusreport)
	      report(SS,"MX-lookup: %s", host);

	    SS->mxcount = 0;
	    memset(SS->mxh, 0, sizeof(SS->mxh));

	    realname[0] = 0;
	    realnamettl = 86400; /* Max cache age.. */
	    rc = getmxrr(SS, host, SS->mxh, MAXFORWARDERS, 0,
			 realname, sizeof(realname), &realnamettl);
	    realnamettl += now;

	    if (rc == EX_OK) {
	      mxsetsave(SS, host);
	      add_cname_cache(SS, host, *realname ? realname : NULL, realnamettl);
	    }

	    if (SS->verboselog) {
	      if (SS->mxcount == 0)
		fprintf(SS->verboselog,
			" rc=%d, no MXes (host='%.200s'; realname='%.200s')\n", rc, host, realname);
	      else
		fprintf(SS->verboselog,
			" rc=%d, mxh[0].host=%.200s (host='%.200s', realname='%.200s') mxcnt=%d\n",
			rc, (SS->mxh[0].host) ? (char*)SS->mxh[0].host : "<NUL>",
			host, realname, SS->mxcount);
	    }

	    /* Some error from getmxrr(), bail out immediately */
	    if (rc != EX_OK)
	      return rc;

	  }
#endif /* BIND */

	  if (!checkwks && SS->mxcount > 0 && SS->mxh[0].host == NULL) {

	    /* Condition ( SS->mxcount > 0 && SS->mxh[0].host == NULL ) can
	       be considered as: Instant (Configuration?) Error;
	       No usable MXes, possibly we are at the lowest MX priority level,
	       and somebody has made some configuration errors... */

	    strcpy(SS->remotemsg,
		   "smtp; 500 (configuration inconsistency, we are lowest MX, but this is not our local domain!)");
	    notaryreport(NULL, NULL,
			 "5.4.4 (unable to route)",
			 "smtp; 500 (configuration inconsistency, we are lowest MX but this is not our local domain)");

	    return EX_NOHOST;
	  }

	  if (SS->mxcount == 0 || SS->mxh[0].host == NULL) {

	    struct addrinfo req, *ai;

	    memset(&req, 0, sizeof(req));
	    req.ai_socktype = SOCK_STREAM;
	    req.ai_protocol = IPPROTO_TCP;
	    req.ai_flags    = AI_CANONNAME;
	    req.ai_family   = PF_INET;

	    ai = NULL;

	    errno = 0;
	    /* Either forbidden MX usage, or does not have MX entries! */

#ifdef HAVE_GETADDRINFO
	    r = getaddrinfo(host, "0", &req, &ai);
#else
	    r = _getaddrinfo_(host, "0", &req, &ai, SS->verboselog);
#endif
	    if (SS->verboselog)
	      fprintf(SS->verboselog,"getaddrinfo(INET,'%s') -> r=%d, ai=%p\n",host,r,ai);

#if defined(AF_INET6) && defined(INET6)
	    if (use_ipv6) {
	      struct addrinfo *ai2 = NULL, **aip;
	      int i2;

	      memset(&req, 0, sizeof(req));
	      req.ai_socktype = SOCK_STREAM;
	      req.ai_protocol = IPPROTO_TCP;
	      req.ai_flags    = AI_CANONNAME;
	      req.ai_family   = PF_INET6;

	      /* This resolves CNAME, it should not happen in case
		 of MX server, though..    */
#ifdef HAVE_GETADDRINFO
	      i2 = getaddrinfo(host, "0", &req, &ai2);
#else
	      i2 = _getaddrinfo_(host, "0", &req, &ai2, SS->verboselog);
#endif
	      if (SS->verboselog)
		fprintf(SS->verboselog,
			"  getaddrinfo(INET6,'%s') -> r=%d, ai=%p\n",
			host,i2,ai2);

	      if (r != 0 && i2 == 0) {
		/* IPv6 address, no IPv4 (or error..) */
		r = i2;
		ai = ai2; ai2 = NULL;
	      }
	      if (ai2 && ai) {
		/* BOTH ?!  Catenate them! */
		aip = &(ai->ai_next);
		while (*aip) aip = &((*aip)->ai_next);
		*aip = ai2;
	      }
	    }
#endif
	    if (r != 0) {

	      int gai_err = r;

	      /* getaddrinfo() yields no data, and getmxrr() yielded
		 EX_TEMPFAIL ?   Well, getmxrr() did set some reports,
		 lets use them! */
	      if ((r == EAI_NONAME || r == EAI_AGAIN) && rc == EX_TEMPFAIL)
		return EX_DEFERALL;

	      if ( r == EAI_AGAIN ) {

		sprintf(SS->remotemsg,"smtp; 566 (getaddrinfo<%.200s>: try later)",host);
		time(&endtime);
		notary_setxdelay((int)(endtime-starttime));
		notaryreport(NULL,FAILED,"5.4.3 (dns lookup 'try again')", SS->remotemsg);
		if (SS->verboselog)
		  fprintf(SS->verboselog,"%s\n",SS->remotemsg+6);
		if (ai != NULL)
		  freeaddrinfo(ai);
		return EX_DEFERALL;
	      }

#ifdef EAI_NODATA
	      if ( r == EAI_NODATA ) {
		sprintf(SS->remotemsg,"smtp; 500 (getaddrinfo<%.200s>: No data)",host);
		time(&endtime);
		notary_setxdelay((int)(endtime-starttime));
		notaryreport(NULL,FAILED,"5.4.3 (dns lookup 'no data')", SS->remotemsg);
		if (SS->verboselog)
		  fprintf(SS->verboselog,"%s\n",SS->remotemsg+6);
		if (ai != NULL)
		  freeaddrinfo(ai);
		if (rc == EX_TEMPFAIL)
		  return EX_DEFERALL;
		return EX_UNAVAILABLE;
	      }
#endif
	      r = EX_UNAVAILABLE; /* This gives instant rejection */
	      if (rc == EX_TEMPFAIL) r = rc;

	      if (strchr(host,'_') != NULL) {
		sprintf(SS->remotemsg,
			"smtp; 500 (Hostname with illegal [to the DNS] underscore in it: '%.200s')", host);
	      } else if (noMX) {
		sprintf(SS->remotemsg,
			"smtp; 500 (configuration inconsistency. MX usage forbidden, no address in the DNS: '%.200s')", host);
	      } else {
		if (SS->mxcount > 0) {
		  sprintf(SS->remotemsg,
			  "smtp; 500 (nameserver data inconsistency. All MXes rejected [we are the best?], no address: '%.200s')", host);
#if 1
		  zsyslog((LOG_NOTICE, "%s", SS->remotemsg));
		  if (r != EX_TEMPFAIL)
		    r = EX_NOHOST;
#endif
		} else if (gai_err == EAI_NONAME
#ifdef EAI_NODATA
			   || gai_err == EAI_NODATA
#endif
			   ) {
		  sprintf(SS->remotemsg,
			  "smtp; 500 (nameserver data inconsistency. No MX, no address: '%.200s' (%s))",
			  host, gai_err == EAI_NONAME ? "NONAME" : "NODATA");
		  zsyslog((LOG_NOTICE, "%s r=%d", SS->remotemsg, r));
#if 0
		  if (r != EX_TEMPFAIL)
		    r = EX_NOHOST; /* Can do instant reject */
#else
		  r = EX_TEMPFAIL;
#endif
		} else {
		  sprintf(SS->remotemsg,
			  "smtp; 500 (nameserver data inconsistency. No MX, no address: '%.200s', errno=%s, gai_errno='%s')",
			  host, strerror(errno), gai_strerror(gai_err));
#if 1
		  zsyslog((LOG_NOTICE, "%s", SS->remotemsg));
		  r = EX_TEMPFAIL; /* This gives delayed rejection (after a timeout) */
#endif
		}
	      }
	      time(&endtime);
	      notary_setxdelay((int)(endtime-starttime));
	      notaryreport(NULL,FAILED,"5.4.4 (nameserver data inconsistency)",
			   SS->remotemsg);
	      if (SS->verboselog)
		fprintf(SS->verboselog,"%s\n",SS->remotemsg+6);
	      /* it was: EX_UNAVAILABLE, but such blocks retrying, thus
		 current EX_TEMPFAIL, which will cause timeout later on.. */
	      if (ai != NULL)
		freeaddrinfo(ai);

	      /* We translate these TEMPFAILs to DEFERALLs! */
	      if (r == EX_TEMPFAIL) r = EX_DEFERALL;

	      return r;
	    }
	    {
	      char buf[512];
	      sprintf(buf,"dns; %.200s", host);
	      notary_setwtt(buf);
	    }
	    if (noMX == -2)
	    	retval = makeconn(SS, host, ai, -2);
	    else
	    	retval = makeconn(SS, host, ai, -1);

	    if (ai != NULL)
	      freeaddrinfo(ai);

	  } else {

	    /* Has valid MX records, they have been suitably randomized
	       at  getmxrr(), and are now ready for use.  */

	    retval = EX_TEMPFAIL;

	    for (i = SS->firstmx; (i < SS->mxcount &&
				   SS->mxh[i].host != NULL); ++i) {

	      char buf[512];
	      sprintf(buf,"dns; %.200s", SS->mxh[i].host);
	      notary_setwtt(buf);

	      r = makeconn(SS, SS->mxh[i].host, SS->mxh[i].ai, i);
	      SS->firstmx = i+1;
	      if (r == EX_OK) {
		retval = EX_OK;
		break;
	      } else if (r == EX_TEMPFAIL || r == EX_DEFERALL)
		retval = r;
	    }
	  }
	} /* end of HOSTNAME MX lookup processing */

 bail_out:

	if (debug && logfp)
	  fprintf(logfp,
		  "%s#\tsmtpconn: retval = %d\n", logtag(), retval);

	return retval;
}

void
deducemyifname(SS)
	SmtpState *SS;
{
	Usockaddr laddr;
	size_t laddrsize;
	struct hostent *hp;

	if (SS->myhostname != NULL)
	  free(SS->myhostname);
	SS->myhostname = NULL;

	laddrsize = sizeof(laddr);
	if (getsockname(sffileno(SS->smtpfp), (struct sockaddr*) &laddr,
			&laddrsize) != 0)
	  return; /* Failure .. */

	if (laddr.v4.sin_family == AF_INET)
	  hp = gethostbyaddr((char*)&laddr.v4.sin_addr,   4, AF_INET);
#if defined(AF_INET6) && defined(INET6)
	/* No need to check for IPv4-MAPPED addresses here.
	   Presumption is: If connection is made with IPv4 socket,
	   laddr is of IPv4 type. If connection is made with IPv6,
	   the destination is presumably also of IPv6, and thus
	   a mapped address here is most unlikely..  */
	else if (laddr.v6.sin6_family == AF_INET6)
	  hp = gethostbyaddr((char*)&laddr.v6.sin6_addr, 16, AF_INET6);
#endif
	else
	  hp = NULL;

	if (hp == NULL)
	  return;

	/* Ok, NOW we have a hostent with our IP-address reversed to a name */
	SS->myhostname = strdup(hp->h_name);
}

int
makeconn(SS, hostname, ai, ismx)
	SmtpState *SS;
	const char *hostname;
	struct addrinfo *ai;
	int ismx;
{
	int retval;
	int mfd;
	int isreconnect = (ai == &SS->ai);
	char	hostbuf[MAXHOSTNAMELEN+1];

	MIBMtaEntry->tasmtp.SmtpStarts += 1;

#ifdef	BIND
#ifdef	RFC974
	{
	  int	ttl;
	
	  if (ai->ai_canonname)
	    strncpy(hostbuf, ai->ai_canonname, sizeof(hostbuf));
	  else if (hostname)
	    strncpy(hostbuf, hostname, sizeof(hostbuf));
	  else
	    *hostbuf = 0;
	  hostbuf[sizeof(hostbuf)-1] = 0;
	
	  if (checkwks && SS->verboselog)
	    fprintf(SS->verboselog,"  makeconn(): checkwks of host %.200s\n",
		    hostbuf);
	
	  if (checkwks &&
	      getrr(hostbuf, &ttl, sizeof hostbuf, (u_short)T_WKS, 2, SS->verboselog) != 1) {
	    sprintf(SS->remotemsg,"smtp; 550 (WKS checks: no SMTP reception capability registered for host %.200s)",
		    hostbuf);
	    time(&endtime);
	    notary_setwttip(NULL);
	    notary_setxdelay((int)(endtime-starttime));
	    notaryreport(NULL,FAILED,"5.4.4 (WKS Checks: no SMTP reception capability registered)", SS->remotemsg);
	    if (SS->verboselog)
	      fprintf(SS->verboselog,"%s\n",SS->remotemsg+6);
	    return EX_UNAVAILABLE;
	  }
	}
#endif	/* RFC974 */
#endif	/* BIND */

	retval = EX_DEFERALL;
#if 0
	if (SS->verboselog) {
	  fprintf(SS->verboselog,"makeconn('%.200s') to IP addresses:", hostbuf);
	  for ( ; ai ; ai = ai->ai_next ) {
	    /* XX: print the addresses... */
	    fprintf(SS->verboselog," %s",
		    dottedquad((struct in_addr*)*hp_getaddr()));
	  }
	  fprintf(SS->verboselog,"\n");
	}
#endif

	for ( ; ai && !getout ; ai = ai->ai_next ) {

	  int i = 0;
	  struct sockaddr_in *si;
#if defined(AF_INET6) && defined(INET6)
	  struct sockaddr_in6 *si6;
#endif

	  if (! isreconnect) {

	    /* For possible reconnect */
	    if (SS->ai.ai_canonname) free(SS->ai.ai_canonname);
	    SS->ai.ai_canonname = NULL;
	    memcpy(&SS->ai, ai, sizeof(*ai));
	    memset(&SS->ai_addr, 0, sizeof(SS->ai_addr));
	    if (ai->ai_family == AF_INET)
	      memcpy(&SS->ai_addr.v4, ai->ai_addr, sizeof(SS->ai_addr.v4));
#if defined(AF_INET6) && defined(INET6)
	    else
	      memcpy(&SS->ai_addr.v6, ai->ai_addr, sizeof(SS->ai_addr.v6));
#endif
	    SS->ai.ai_addr = (struct sockaddr *) & SS->ai_addr;
	    SS->ai.ai_canonname = NULL;
	    if (ai->ai_canonname)
	      SS->ai.ai_canonname = strdup(ai->ai_canonname);
	    else if (hostname)
	      SS->ai.ai_canonname = strdup(hostname);
	    SS->ai.ai_next = NULL;
	    SS->ismx = ismx;
	  }

	  switch (ai->ai_family) {
	  case AF_INET:
	    si = (struct sockaddr_in *)ai->ai_addr;
	    i = matchmyaddress((Usockaddr *) ai->ai_addr);
	    inet_ntop(AF_INET, &si->sin_addr, SS->ipaddress, sizeof(SS->ipaddress));
	    sprintf(SS->ipaddress + strlen(SS->ipaddress), "|%d",
		    SS->servport);
	    break;
#if defined(AF_INET6) && defined(INET6)
	  case AF_INET6:
	    si6 = (struct sockaddr_in6*)ai->ai_addr;
	    i = matchmyaddress((Usockaddr *)ai->ai_addr);
	    strcpy(SS->ipaddress,"ipv6 ");
	    inet_ntop(AF_INET6, &si6->sin6_addr, SS->ipaddress+5, sizeof(SS->ipaddress)-5);
	    sprintf(SS->ipaddress + strlen(SS->ipaddress), "|%d",
		    SS->servport);
	    break;
#endif
#ifdef AF_UNIX
	  case AF_UNIX:
	    {
	      struct sockaddr_un *un = (struct sockaddr_un *)ai->ai_addr;
	      sprintf(SS->ipaddress, "UNIX:%s", un->sun_path);
	    }
	    break;
#endif
	  default:
	    sprintf(SS->ipaddress,"UNKNOWN-ADDR-FAMILY-%d", ai->ai_family);
	    break;
	  }

	  notary_setwttip(SS->ipaddress);

	  if (i != 0 && ismx == -2)
	    i = 0; /* Allow routing back to [1.2.3.4] ! */

	  if (SS->verboselog)
	    fprintf(SS->verboselog,"Trying address: %s port %d\n",
		    SS->ipaddress, SS->servport);

	  /* XXX: Locally matched address is on some MX target, if  ismx >= 0.
	     In such a case, the error should be ???? What ? */

	  if (i != 0 && SS->servport == IPPORT_SMTP) {
	    time(&endtime);
	    notary_setxdelay((int)(endtime-starttime));
	    switch (i) {
	    case 3:
	      notaryreport(NULL,FAILED,"5.4.6 (trying to use invalid destination address)","smtp; 500 (Trying to talk to invalid destination network address!)");
	      break;
	    case 2:
	      notaryreport(NULL,FAILED,"5.4.6 (trying to talk to loopback (=myself)!)","smtp; 500 (Trying to talk to loopback (=myself)!)");
	      break;
	    default:
	      notaryreport(NULL,FAILED,"5.4.6 (trying to talk with myself!)","smtp; 500 (Trying to talk with myself!)");
	      break;
	    }
	    sprintf(SS->remotemsg,"Trying to talk with myself!");
	    retval = EX_UNAVAILABLE;
	    break;		/* TEMPFAIL or UNAVAILABLE.. */
	  }

	  if (SS->smtpfp) {
	    /* Clean (close) these fds -- they have been noted to leak.. */
	    smtpclose(SS, 1);
	    if (logfp)
	      fprintf(logfp,"%s#\t(closed SMTP channel at makeconn())\n",logtag());
	  }


	  i = vcsetup(SS, /* (struct sockaddr*) */ ai->ai_addr, &mfd, hostbuf);
	  retval = i;

	  switch (i) {
	  case EX_OK:

	      if (lmtp_mode)
		MIBMtaEntry->tasmtp.LmtpConnects  += 1;
	      else
		MIBMtaEntry->tasmtp.SmtpConnects  += 1;

	      SS->smtpfd = mfd;
	      SS->smtpfp = sfnew(NULL, NULL, SS->smtp_bufsize, mfd, SF_WRITE);

	      memset(&SS->smtpdisc, 0, sizeof(SS->smtpdisc));
	      SS->smtpdisc.D.readf   = NULL;
	      SS->smtpdisc.D.writef  = smtp_sfwrite;
	      SS->smtpdisc.D.seekf   = NULL;
	      SS->smtpdisc.D.exceptf = NULL;
	      SS->smtpdisc.SS        = SS;
	      sfdisc(SS->smtpfp, &SS->smtpdisc.D);
	      SS->lasterrno          = 0;

	      if (SS->smtpfp == NULL) {
		int err;
		err = errno;
		fprintf(stdout,"# smtp: Failed to fdopen() a socket stream, errno=%d, err='%s' Hmm ??\n",err, strerror(err));
		fflush(stdout);
		abort(); /* sock-stream fdopen() failure! */
	      }

	      MIBMtaEntry->tasmtp.SmtpConnectsCnt += 1;
	      ++ net_socks_open_cnt;

	      deducemyifname(SS);

	      SS->smtp_outcount = 0;
	      SS->block_written = 0;

	      SS->do_rset     = 0;

	      if (SS->esmtp_on_banner > 0)
		SS->esmtp_on_banner = 0;

	      /* Wait for the initial "220-" greeting */
	      timeout = timeout_cmd;
	      SS->rcptstates = 0;
	      retval = smtpwrite(SS, 1, NULL, 0, NULL);

	      if (logfp)
		fprintf(logfp,"%s#\t('220' expectance did yield %d )\n",
			logtag(), retval);

	      if (retval != EX_OK)
		/*
		 * If you want to continue with the next host,
		 * the below should be 'return EX_TEMPFAIL'.
		 */
		break;		/* try another host address */

	      if (SS->verboselog)
		fprintf(SS->verboselog,"Connection attempt did yield code %d / %s\n", retval, sysexitstr(retval));
	      return EX_OK;

	  default:
	      MIBMtaEntry->tasmtp.SmtpConnectFails  += 1;
	      if (logfp)
		fprintf(logfp,"%s#\t(vcsetup() did yield %d )\n",logtag(), i);
	      break;
	  }
	} /* end of for-loop */

	if (getout)
	  retval = EX_TEMPFAIL;

	if (SS->verboselog)
	  fprintf(SS->verboselog,"Connection attempt did yield code %d / %s\n", retval, sysexitstr(retval));

	return retval;
}

int
makereconn(SS)
     SmtpState *SS;
{
  smtpclose(SS, 1);
  return makeconn(SS, SS->ai.ai_canonname, & SS->ai, SS->ismx);
}

int
vcsetup(SS, sa, fdp, hostname)
	SmtpState *SS;
	struct sockaddr *sa;
	int *fdp;
	char *hostname;
{
	int af, port;
	int addrsiz;
	int sk, rc;
	Usockaddr *sai = (Usockaddr *)sa;
	Usockaddr sad;
	int wantbindaddr = 0;
	Usockaddr upeername;
	size_t upeernamelen = 0;

	u_short p;
	int errnosave, flg;
	char *se;

	time(&now);

	af = sa->sa_family;
	switch (af) {
#if defined(AF_INET6) && defined(INET6)
	case AF_INET6:
	  addrsiz = sizeof(sai->v6);
	  memset(&sad.v6, 0, sizeof(sad.v6));
	  break;
#endif
#ifdef AF_UNIX
	case AF_UNIX:
	  {
	    struct sockaddr_un *sau = (struct sockaddr_un *)sa;
	    addrsiz = 3 + strlen( sau->sun_path );
	  }
	  break;
#endif
	default: /* PRESUME: AF_INET */
	  addrsiz = sizeof(sai->v4);
	  memset(&sad, 0, sizeof(sad));
	  break;
	}

	if (conndebug)
	  fprintf(stderr, "Trying %.200s [%.200s] ... ",
		  hostname, SS->ipaddress);
	if (logfp)
	  fprintf(logfp, "%s#\t(Connecting to `%.200s' [%.200s] %24.24s)\n",
		  logtag(), hostname, SS->ipaddress, ctime(&now));
	strncpy(SS->remotehost, hostname, sizeof(SS->remotehost));
	SS->remotehost[sizeof(SS->remotehost)-1] = 0;
	if (statusreport) {
	  report(SS,"connecting to [%s]",SS->ipaddress);
	}

	smtp_flush(SS); /* Flush in every case */

	SS->writeclosed = 0;

	sk = socket(af, SOCK_STREAM, 0);
	if (sk < 0) {
	  se = strerror(errno);
	  sprintf(SS->remotemsg, "smtp; 500 (Internal error, socket(AF=%d): %s)", af, se);
	  time(&endtime);
	  notary_setxdelay((int)(endtime-starttime));
	  notaryreport(NULL,FAILED,"5.4.0 (internal error)",SS->remotemsg);
	  if (conndebug)
	    fprintf(stderr, "%s\n", SS->remotemsg+6);
	  if (SS->verboselog)
	    fprintf(SS->verboselog,"%s\n",SS->remotemsg+6);
	  if (logfp)
	    fprintf(logfp,"%s#\t(Internal error, socket: %s)\n",logtag(),se);
abort();
	  return EX_TEMPFAIL;
	}

	wantbindaddr = !zgetbindaddr(localidentity, af, &sad); 
	if (localidentity && logfp)
	  fprintf(logfp, "%s#\tlocalidentity=%s wantbindaddr=%d\n",
		  logtag(), localidentity, wantbindaddr);

	if (wantreserved && getuid() == 0) {
	  /* try grabbing a port */
	  for (p = IPPORT_RESERVED-1; p >= (u_short)(IPPORT_RESERVED/2); --p) {
	    if (af == AF_INET) {
	      sad.v4.sin_family = AF_INET;
	      sad.v4.sin_port   = htons(p);
	      rc = bind(sk, (struct sockaddr *)&sad, sizeof sad.v4);
	      if (rc >= 0)
		break;
	    }
#if defined(AF_INET6) && defined(INET6)
	    else if (af == AF_INET6) {
	      sad.v6.sin6_family = AF_INET6;
	      sad.v6.sin6_port   = htons(p);
	      rc = bind(sk, (struct sockaddr *)&sad, sizeof sad.v6);
	      if (rc >= 0)
		break;
	    }
#endif
	    if (errno != EADDRINUSE && errno != EADDRNOTAVAIL) {
	      char *s = strerror(errno);
	      sprintf(SS->remotemsg, "smtp; 500 (Internal error, bind: %s)", s);
	      time(&endtime);
	      notary_setxdelay((int)(endtime-starttime));
	      notaryreport(NULL,FAILED,"5.4.0 (internal error, bind)",SS->remotemsg);
	      if (SS->verboselog)
		fprintf(SS->verboselog,"%s\n", SS->remotemsg+6);
	      if (conndebug)
		fprintf(stderr, "%s\n", SS->remotemsg+6);
	      if (logfp)
		fprintf(logfp, "%s#\t(Internal error, bind: %s)\n", logtag(), s);
	      return EX_UNAVAILABLE;
	    }
	  }

	  if (p < (u_short)(IPPORT_RESERVED/2)) {
	    sprintf(SS->remotemsg, "too many busy ports");
	    time(&endtime);
	    notary_setxdelay((int)(endtime-starttime));
	    notaryreport(NULL,FAILED,"5.4.0 (internal error, too many busy ports)","smtp; 500 (Internal error, too many busy ports)");
	    if (conndebug)
	      fprintf(stderr, "%s\n", SS->remotemsg+6);
	    if (SS->verboselog)
	      fprintf(SS->verboselog,"%s\n",SS->remotemsg+6);
	    if (logfp)
	      fprintf(logfp,"%s#\t(Internal error, too many busy ports)\n", logtag());
	    return EX_TEMPFAIL;
	  }
	} else if (wantbindaddr) {
	  /* Ok, it wasn't a desire for any PRIVILEGED port, just
	     binding on the specific IP will be accepted. */
	  errno = 0;
	  rc = -2;
	  if (af == AF_INET)
	    rc = bind(sk, (struct sockaddr *)&sad, sizeof sad.v4);
#if defined(AF_INET6) && defined(INET6)
	  if (af == AF_INET6)
	    rc = bind(sk, (struct sockaddr *)&sad, sizeof sad.v6);
#endif
	  if (logfp)
	    fprintf(logfp,"%s#\tlocalidentity=%s bind() rc=%d errno = %d\n",
		    logtag(), localidentity, rc, errno);
	  /* If it fails, what could we do ? */
	}

	port = SS->servport;
	if (SS->literalport > 0)
	  port = SS->literalport;
	switch (af) {
	case AF_INET:
	  sai->v4.sin_port   = htons(port);
	  break;
#if defined(AF_INET6) && defined(INET6)
	case AF_INET6:
	  sai->v6.sin6_port = htons(port);
	  break;
#endif
	}

	/* setreuid(0,first_uid);
	   if(SS->verboselog) fprintf(SS->verboselog,"setreuid: first_uid=%d, ruid=%d, euid=%d\n",first_uid,getuid(),geteuid()); */

	if (SS->verboselog) {
	  switch (af) {
	  case AF_INET:
#if defined(AF_INET6) && defined(INET6)
	  case AF_INET6:
#endif
	    fprintf(SS->verboselog, "Connecting to %s [%s] port %d\n",
		    hostname, SS->ipaddress, ntohs(sai->v4.sin_port));
	    break;
#ifdef AF_UNIX
	  case AF_UNIX:
	    fprintf(SS->verboselog, "Connecting to %s [%s]\n",
		    hostname, SS->ipaddress);
	    break;
#endif
	  default:
	    fprintf(SS->verboselog, "Connecting to %s [UNKNOWN-ADDRESS-FAMILY-%d]\n",
		    hostname, af);
	    break;
	  }
	}

	gotalarm = 0;

	/* The socket will be non-blocking for its entire lifetime.. */
	fd_nonblockingmode(sk);

	errnosave = errno = 0;

	smtp_flush(SS);
	SS->cmdstate = SMTPSTATE_CONNECT;

	if (sa->sa_family == AF_INET) {
	  struct sockaddr_in *si = (struct sockaddr_in*) sa;
	  unsigned long  ia = ntohl(si->sin_addr.s_addr);
	  int anet = ia >> 24;
	  if (anet <= 0 || anet >= 224) {
	    close(sk);
	    errno = EADDRNOTAVAIL;
	    return EX_UNAVAILABLE;
	  }
	}

	
	if (connect(sk, sa, addrsiz) < 0 &&
	    (errno == EWOULDBLOCK || errno == EINPROGRESS)) {

	  /* Wait for the connection -- or timeout.. */

	  long tv;
	  static struct zmpollfd *fds = NULL;
	  int fdscount = 0;
	  int rc;

	  errno = 0;

	  /* Pick our local socket name */
	  /* NOTE: At Solaris 2.5.1 (STREAMS based) this may take
	     lots of time! */

	  memset(&upeername, 0, sizeof(upeername));
	  upeernamelen = sizeof(upeername);
	  getsockname(sk, (struct sockaddr*) &upeername, &upeernamelen);

	  errnosave = errno;

	  /* Select for the establishment, or for the timeout */

	  tv = timeout_conn;

	  zmpoll_addfd(&fds, &fdscount, -1, sk, NULL); /* FOR WRITE */
	  rc = zmpoll(fds, fdscount, tv * 1000);

	  errno = 0; /* All fine ? */
	  if (rc == 0) {
	    /* Timed out :-( */
	    gotalarm = 1; /* Well, sort of ... */
	    errno = ETIMEDOUT;
	  }
	}

	if (!errnosave)
	  errnosave = errno;

#ifdef SO_ERROR
	flg = 0;
	if (errnosave == 0) {
	  size_t flglen = sizeof(flg);
	  getsockopt(sk, SOL_SOCKET, SO_ERROR, (void*)&flg, &flglen);
	}
	if (flg != 0 && errnosave == 0)
	  errnosave = flg;
	/* "flg" contains socket specific error condition data */
#endif

	if (errnosave == 0) {
	  /* We have successfull connection,
	     lets record its peering data */
	  memset(&upeername, 0, sizeof(upeername));
	  upeernamelen = sizeof(upeername);
	  getsockname(sk, (struct sockaddr*) &upeername, &upeernamelen);
	}

	if (upeernamelen != 0) {
#if defined(AF_INET6) && defined(INET6)
	  if (upeername.v6.sin6_family == AF_INET6) {
	    int len = strlen(SS->ipaddress);
	    char *s = SS->ipaddress + len;
	    strcat(s++, "|");
	    inet_ntop(AF_INET6, &upeername.v6.sin6_addr,
		      s, sizeof(SS->ipaddress)-len-9);
	    s = s + strlen(s);
	    sprintf(s, "|%d", ntohs(upeername.v6.sin6_port));
	  } else
#endif
	    if (upeername.v4.sin_family == AF_INET) {
	      int len = strlen(SS->ipaddress);
	      char *s = SS->ipaddress + len;
	      strcat(s++, "|");
	      inet_ntop(AF_INET, &upeername.v4.sin_addr,
			s, sizeof(SS->ipaddress)-len-9);
	      s = s + strlen(s);
	      sprintf(s, "|%d", ntohs(upeername.v4.sin_port));
	    } else {
	      strcat(SS->ipaddress, "|UNKNOWN-LOCAL-ADDRESS");
	    }

	  notary_setwttip(SS->ipaddress);
	}

	if (errnosave == 0 && !gotalarm) {
	  int on = 1;
	  /* setreuid(0,0); */
	  *fdp = sk;

#ifdef SO_KEEPALIVE
#if 1
	  setsockopt(sk, SOL_SOCKET, SO_KEEPALIVE, (void*)&on, sizeof on);
#else
#if	defined(__svr4__) || defined(BSD) && (BSD-0) >= 43
	  setsockopt(sk, SOL_SOCKET, SO_KEEPALIVE, (void*)&on, sizeof on);
#else  /* BSD < 43 */
	  setsockopt(sk, SOL_SOCKET, SO_KEEPALIVE, 0, 0);
#endif /* BSD >= 43 */
#endif
#endif

#ifdef SO_SNDBUF
	  if (sockwbufsize > 0) {
	    on = sockwbufsize;
#if 1
	    setsockopt(sk, SOL_SOCKET, SO_SNDBUF, (void*)&on, sizeof on);
#else
#if	defined(__svr4__) || defined(BSD) && (BSD-0) >= 43
	    setsockopt(sk, SOL_SOCKET, SO_SNDBUF, (void*)&on, sizeof on);
#else  /* BSD < 43 */
	    setsockopt(sk, SOL_SOCKET, SO_SNDBUF, 0, 0);
#endif /* BSD >= 43 */
#endif
	  }
#endif

	  if (conndebug)
	    fprintf(stderr, "connected!\n");

	  return EX_OK;
	}
	/* setreuid(0,0); */

	se = strerror(errnosave);

	sprintf(SS->remotemsg, "smtp; 500 (connect to %.200s [%.200s]: %s)",
		hostname, SS->ipaddress, se);
	if (statusreport)
	  report(SS,"%s",SS->remotemsg+4);
	time(&endtime);
	notary_setxdelay((int)(endtime-starttime));
	notaryreport(NULL,FAILED,"5.4.1 (TCP/IP-connection failure)", SS->remotemsg);

	if (conndebug)
		fprintf(stderr, "%s\n", SS->remotemsg);
	if (SS->verboselog)
		fprintf(SS->verboselog,"%s\n",SS->remotemsg);
	if (logfp)
	  fprintf(logfp,"%s#\t%s\n", logtag(), SS->remotemsg+4);
	close(sk);
	switch (errnosave) {	/* from sendmail... */
	case EBADF:
	case EFAULT:
	case ENOSYS:
#ifdef ENOMSG
	case ENOMSG:
#endif
#ifdef ENOSTR
	case ENOSTR:
#endif
	case ENOTSOCK:
	case EDESTADDRREQ:
	case EMSGSIZE:
	case EPROTOTYPE:
	case ENOPROTOOPT:
	case EPROTONOSUPPORT:
	case ESOCKTNOSUPPORT:
	case EOPNOTSUPP:
	case EPFNOSUPPORT:
	case EAFNOSUPPORT:
		return EX_SOFTWARE;
	case EACCES:
#ifdef ENONET
	case ENONET:
#endif
		return EX_UNAVAILABLE;
	/* wonder how Sendmail missed this one... */
	case EINTR:
	case ENOMEM:
		return EX_TEMPFAIL;
	}
	return EX_DEFERALL;
}


RETSIGTYPE
sig_pipe(sig)
int sig;
{
	if (logfp != NULL) {
	  fprintf(logfp, "%s#\t*** Received SIGPIPE!\n", logtag());
	  /* abort(); */
	}
	SIGNAL_HANDLE(sig, sig_pipe);
	SIGNAL_RELEASE(sig);
}


/*
 *  SMTP PIPELINING (RFC 1854/2197) support uses model of:
 *       1st RCPT is for "MAIL From:<>".. -line
 *       2..n-1: are actual RCPT To:<> -lines
 *	 n:th is the "DATA"-line.
 */


void
smtpclose(SS, failure)
     SmtpState *SS;
     int failure;
{
	if (SS->smtpfp != NULL) {

	  MIBMtaEntry->tasmtp.SmtpConnectsCnt -= 1;
	  -- net_socks_open_cnt;

	  /* First close the socket so that no FILE buffered stuff
	     can become flushed out anymore. */

	  if (SS->smtpfd >= 0)
	    close(SS->smtpfd);
	  SS->smtpfd = -1;
	  /* Absolutely NO SFIO SYNC AT THIS POINT! */
	  zsfsetfd(SS->smtpfp, -1);

	  /* Now do all normal SFIO close things -- including
	     buffer flushes... */

	  sfclose(SS->smtpfp);
	  SS->smtpfp = NULL;
	}

#ifdef HAVE_OPENSSL
	if (SS->TLS.sslmode)
	  tls_stop_clienttls(SS, failure);
	SS->TLS.sslmode = 0;
#endif /* - HAVE_OPENSSL */

	/* Purge former state */
	smtp_flush(SS);
}

void
smtp_flush(SS)
	SmtpState *SS;
{
	int i;

	SS->pipebufsize = 0;
	if (SS->pipebuf == NULL) {
	  SS->pipebufspace = 240;
	  SS->pipebuf = malloc(SS->pipebufspace);
	  if (! SS->pipebuf) zmalloc_failure = 1;
	}
	for (i = 0; i < SS->pipeindex; ++i) {
	  if (SS->pipecmds[i])
	    free(SS->pipecmds[i]);
	  SS->pipecmds[i] = NULL;
	}
	SS->pipeindex   = 0;
	SS->pipereplies = 0;

	SS->rcptstates  = 0;

	SS->prevcmdstate = SMTPSTATE99;
	SS->cmdstate     = SMTPSTATE_MAILFROM;
}


int bdat_flush(SS, lastflg)
	SmtpState *SS;
	int lastflg;
{
	int pos, i, wrlen;
	volatile int r;   /* longjmp() globber danger */
	char lbuf[80];

	if (SS->smtpfp) tcpstream_denagle(sffileno(SS->smtpfp));


	MIBMtaEntry->tasmtp.SmtpBDAT ++;

	if (lastflg)
	  sprintf(lbuf, "BDAT %d LAST", SS->chunksize);
	else
	  sprintf(lbuf, "BDAT %d", SS->chunksize);

	report(SS, "%s", lbuf);

	r = smtpwrite(SS, 1, lbuf, 1 /* ALWAYS "pipeline" */, NULL);

	if (r != EX_OK) {
	  return r;
	}

	for ( pos = 0; pos < SS->chunksize && !sferror(SS->smtpfp); ) {

	  report(SS, "%s - writing: %d/%d", lbuf, pos, SS->chunksize);

	  wrlen = SS->chunksize - pos;
	  i = sfwrite(SS->smtpfp, SS->chunkbuf + pos, wrlen);
	  if (i >= 0)
	    pos += i;
	  else {
	    /* ERROR!!! */
	    SS->chunksize = 0;
	    notaryreport(NULL,NULL,
			 "5.4.2 (BDAT message write failed)",
			 "smtp; 566 (BDAT Message write failed)");
	    report(SS, "%s - write failed; pos=%d/%d", lbuf, r, pos, SS->chunksize);
	    return EX_TEMPFAIL;
	  }
	}

	sfsync(SS->smtpfp);

	if (SS->smtpfp && !sferror(SS->smtpfp)) {
	  if (lastflg || ! SS->pipelining) {
	    r = smtp_sync(SS, r, 0); /* blocking     */
	  } else
	    r = smtp_sync(SS, r, 1); /* non-blocking */
	} else {
	  r = EX_TEMPFAIL;
	  notaryreport(NULL,NULL,
		       "5.4.2 (BDAT message write failed)",
		       "smtp; 566 (BDAT message write failed)");
	}

	report(SS, "%s; wrote %d/%d - rc=%d\n", lbuf, pos, SS->chunksize, r);

	SS->chunksize = 0;

	return r;
}


extern int select_sleep __((int fd, time_t when_tout, int waitwr));


int select_sleep(fd, when_tout, waitwr)
     int fd;
     time_t when_tout;
     int waitwr;
{
	long tv;
	int rc;
	int fdscount = 0;
	static struct zmpollfd *fds = NULL;

	time(&now);

	tv = when_tout - now;
	if (when_tout < now)
	  tv = 0;

	if (waitwr)
	  zmpoll_addfd(&fds, &fdscount, -1, fd, NULL);
	else
	  zmpoll_addfd(&fds, &fdscount, fd, -1, NULL);

	rc = zmpoll( fds, fdscount, tv * 1000 );

	if (rc == 0) /* Timeout w/o input */
	  return -1;
	if (rc == 1) /* There is something to read (or write)! */
	  return 0;

	/* Return soft errors first .. */
	if (errno == EINTR || errno == EAGAIN) return 1;

	return -1;    /* definitely bad things! */
}

int has_readable(fd)
int fd;
{
	int rc;

	static struct zmpollfd *fds = NULL;
	int fdscount = 0;

	zmpoll_addfd(&fds, &fdscount, fd, -1, NULL);

	rc = zmpoll( fds, fdscount, 0 );

	if (rc > 0) /* There is something to read! */
	  return 1;
	return 0;    /* interrupt or timeout, or some such.. */
}

static int code_to_status(code,statusp)
int code;
char **statusp;
{
	int rc;
	char *status;

	switch (code) {
	case 211: /* System status, or system help reply */
	case 214: /* Help message */
	case 220: /* <domain> Service ready */
	case 221: /* <domain> Service closing transmission channel */
	case 250: /* Requested mail action okay, completed */
	case 251: /* User not local; will forward to <forward-path> */
        case 255: /* Something the PMDF 4.1 returns.. for EHLO */
	case 354: /* Start mail input; end with <CRLF>.<CRLF> */
		status = "2.0.0";
		rc = EX_OK;
		break;
	case 421: /* <domain> Service not available, closing transmission channel */
	case 450: /* Requested mail action not taken: mailbox unavailable */
	case 451: /* Requested action aborted: local error in processing */
	case 452: /* Requested action not taken: insufficient system storage */
		status = "4.0.0";
		rc = EX_TEMPFAIL;
		break;
	case 455: /* ESMTP parameter failure */
		status = "5.5.4";
		rc = EX_USAGE;
		break;
	case 501: /* Syntax error in parameters or arguments */
		status = "5.5.2";
		rc = EX_USAGE;
		break;
	case 500: /* Syntax error, command unrecognized */
	case 502: /* Command not implemented */
		status = "5.5.1";
		rc = EX_PROTOCOL;
		break;
	case 503: /* Bad sequence of commands */
		status = "5.5.0";
		rc = EX_TEMPFAIL;
		break;
	case 504: /* Command parameter not implemented */
		status = "5.5.4";
		rc = EX_PROTOCOL;
		break;
	case 550: /* Requested action not taken: mailbox unavailable */
		status = "5.1.1 (bad destination mailbox)";
		rc = EX_NOUSER;
		break;
	case 551: /* User not local; please try <forward-path> */
		status = "5.1.6 (mailbox has moved)";
		rc = EX_NOUSER;
		break;
	case 552: /* Requested mail action aborted: exceeded storage allocation */
		status = "5.2.3 (Some content related rejection, size ? text ?)";
		rc = EX_UNAVAILABLE;
		break;
	case 553: /* Requested action not taken: mailbox name not allowed */
		status = "5.1.3 (bad destination mailbox address [syntax])";
		rc = EX_NOUSER;
		break;
	case 554:
		status = "5.1.1 (No acceptable recipients given)";
		rc = EX_NOUSER;
		break;
	case 555: /* Unknown MAIL From:<>/RCPT To:<> parameter */
		status = "5.5.4 (invalid parameters)";
		rc = EX_USAGE;
		break;
	case 571:
		status = "5.7.1 (Delivery not authorized, message refused)";
		rc = EX_NOUSER;
		break;
	default:
		switch (code/100) {
		case 2:
		case 3:
			status = "2.0.0 (generic ok)";
			rc = EX_OK;
			break;
		case 4:
			status = "4.0.0 (generic temporary failure)";
			rc = EX_TEMPFAIL;
			break;
		case 5:
			status = "5.0.0 (generic permanent failure)";
			rc = EX_UNAVAILABLE;
			break;
		default:
			status = "5.5.0 (generic protocol failure)";
			rc = EX_TEMPFAIL;
			break;
		}
		break;
	}
	*statusp = status;
	return rc;
}


int
smtp_sync(SS, r, nonblocking)
	SmtpState *SS;
	int r, nonblocking;
{
	char *s, *eof, *eol, *eol2;
	int idx  = 0, nextidx, code = 0;
	int rc   = EX_OK, len;
	int err  = 0;
	int i, found_any;
	char buf[512];
	char *p;
	char *status = NULL;
	int statesave;
	time_t when_timeout;

	SS->smtp_outcount = 0;
	SS->block_written = 0;

	eol = SS->pipebuf;

#if 0
	if (SS->verboselog)
	  fprintf(SS->verboselog, "smtp_sync(SS, r=%d, nonblocking=%d)  idx=%d\n", r, nonblocking, SS->pipereplies);
#endif
	if (logfp)
	  fprintf(logfp,"%s#\tsmtp_sync(SS, r=%d, nonblocking=%d)  idx=%d\n", logtag(), r, nonblocking, SS->pipereplies);

	if (SS->pipereplies == 0) {
	  SS->continuation_line = 0;
	  SS->first_line = 1;
	}

	if (!nonblocking && SS->smtpfp && sffileno(SS->smtpfp) >= 0)
	  sfsync(SS->smtpfp);			/* Flush output */

	/*
	   We have TWO exceptions of the rule about "one reply per
	   pipereplies count"; Namely "BDAT nn LAST" MAY yield zero
	   or more replies in LMTP mode, and its sender has *no* clue
	   about when that may happen.  While DATA's "dot" knows how
	   many it needs to pick, things are cleaner when we treat it
	   similarly to "BDAT nn LAST".

	   To recognize when this is the case:
	       lmtp_mode && (idx == (SS->pipeindex-1)) &&
	       SS->cmdstate >= SMTPSTATE_DATADOT

	   At the begin of the loop we must check if there are any
	   nondiagnosed recipients left.  If none are, we exit the loop.

	*/
	   

	for (idx = SS->pipereplies; idx < SS->pipeindex; idx = nextidx) {

	  struct rcpt *datarp = NULL;

	  nextidx = idx+1;

	  /* Collect MULTIPLE missing replies IF WE ARE 1) IN LMTP MODE,
	     2) at the last item of commands, 3) we are at the DOT of
	     DATA or at BDAT LAST phase. */

	  found_any = 0;
	  if (lmtp_mode && (idx == (SS->pipeindex-1)) &&
	      SS->cmdstate >= SMTPSTATE_DATADOT) {

	    for (i = 0; i < idx; ++i) {
	      datarp = SS->pipercpts[i];
	      if (datarp && datarp->lockoffset) {
		found_any = 1;
		nextidx = idx;
		/* 
		   if (SS->verboselog)
		   fprintf(SS->verboselog,
		   " lmtp: Data-dot/bdat-last; i=%d datarp=('%s' '%s' '%s')\n",
		   i, datarp->addr->channel, datarp->addr->host,
		   datarp->addr->user);
		*/
		break;
	      }
	    }
	    if (!found_any)
	      break;

	  } /* Special LMTP BDAT LAST/DATA mode */

      rescan_line_0: /* processed some continuation line */
      rescan_line:   /* Got additional input */
	  s = eol;

	  when_timeout = time(&now) + timeout;

	  eof = SS->pipebuf + SS->pipebufsize;
	  for (eol2 = s; eol2 < eof; ++eol2)
	    if (*eol2 == '\n') break;
	  if (eol2 < eof && *eol2 == '\n') {
	    eol = eol2;
	    ++eol; /* points to char AFTER the newline */
	    if (logfp) {
	      fprintf(logfp,"%s#\t(pipebufsize=%d, s=%d, eol=%d)\n",
		      logtag(), SS->pipebufsize,(int)(s-SS->pipebuf),
		      (int)(eol-SS->pipebuf));
	      /*
	      fprintf(logfp,"%s#\t<< ", logtag());
	      fwrite(SS->pipebuf, 1, (int)(eol-SS->pipebuf), logfp);
	      fprintf(logfp,"\n");
	      */
	    }
	    
	  } else { /* No newline.. Read more.. */
	    int en, waitwr;

	    err = 0;

	  reread_line:

	    /* Blocking read mode */

	    err = 0;
	    len = smtp_nbread(SS, buf, sizeof(buf));
	    waitwr = 0;

	    if (len < 0)
	      err = errno;


#ifdef HAVE_OPENSSL
	    if (SS->TLS.sslmode && err == EPROTO)
	      break;

	    if (SS->TLS.sslmode && SS->TLS.wantreadwrite > 0) waitwr = 1;
#endif /* - HAVE_OPENSSL */

	    if (!nonblocking && len < 0) {

	      /* Blocking mode, and didn't succeed in reading, lets
		 use select to see what we can do. */

	      int infd = SS->smtpfd;

	      if (infd >= 0) {
		err = select_sleep(infd, when_timeout, waitwr);
	      } else {
		err = -1; /* Write has failed, but we still drop here to read.. or something */
	      }

	      en = errno;
	      if (logfp)
		fprintf(logfp,"%s#\tselect_sleep(%d,%d); rc=%d\n",
			logtag(),infd,(int)(when_timeout - now),err);
	      if (err < 0) {
		if (logfp)
		  fprintf(logfp,"%s#\tTimeout (%d sec) while waiting responses from remote (errno=%d)\n",logtag(),timeout,en);
		if (SS->smtpfp) 
		  if (SS->verboselog)
		    fprintf(SS->verboselog,"Timeout (%d sec) while waiting responses from remote\n",timeout);
		rmsgappend(SS, 1, "\rTimeout of %d sec while waiting responses from remote", timeout);

		smtpclose(SS, 1);
		break;
	      }

	      /* select_sleep() indicated that yes, something is available! */
	      goto reread_line;

	    }

	    /* Here we are because we are non-blocking, and have
	       no data, OR we have some data! */

	    if (len < 0) {
	      /* Some error ?? How come ?
		 We have select() confirmed input! */
	      if (nonblocking) {
		if (err == EINTR || err == EAGAIN
#ifdef EWOULDBLOCK
		    || err == EWOULDBLOCK
#endif
		    ) {
		  err = 0;
		  break; /* XX: return ?? */
		}
	      } else { /* blocking mode -- we won't come here ?? */

		if (err == EINTR || err == EAGAIN
#ifdef EWOULDBLOCK
		    || err == EWOULDBLOCK
#endif
		    ) {
		  abort();
		  /*goto reread_line;*/
		}

	      }

	      /* XX: what to do with the error ? */

	      if (logfp)
		fprintf(logfp,"%s#\tRemote gave error %d (%s) while %d responses missing\n",
			logtag(), err, strerror(err), SS->pipeindex - 1 - idx);
	      if (SS->verboselog)
		fprintf(SS->verboselog,"Remote gave error %d (%s) while %d responses missing\n",
			err, strerror(err), SS->pipeindex - 1 - idx);
	      break;
	    } else if (len == 0) {
	      /* The remote hung up! */
	      if (logfp)
		fprintf(logfp,"%s#\tRemote hung up on us while %d responses missing\n",
			logtag(), SS->pipeindex - idx);
	      if (SS->verboselog)
		fprintf(SS->verboselog,"Remote hung up on us while %d responses missing\n",
			SS->pipeindex - idx);
	      rmsgappend(SS, 1,
			 "\rremote hung up on us while %d responses missing",
			 SS->pipeindex - idx);
	      err = EX_TEMPFAIL;
	      break;

	    } else {

	      /* more data for processing.. munch munch.. */
	      if (s > SS->pipebuf) {
		/* Compress the buffer at first */
		int blklen = (s - SS->pipebuf);
		SS->pipebufsize -= blklen;
		if (logfp)
		  fprintf(logfp, "%s#\tCompressing, prevlen=%d taillen=%d",
			  logtag(), blklen, SS->pipebufsize);
		memmove(SS->pipebuf, s, SS->pipebufsize);
		s   = SS->pipebuf;
		eol = SS->pipebuf;
	      }
	      /* Recycling the variable, tell if the block changed */
	      eof = SS->pipebuf;
	      if ((SS->pipebufsize+len+1) > SS->pipebufspace) {
		while ((SS->pipebufsize+len+2) > SS->pipebufspace)
		  SS->pipebufspace <<= 1; /* Double the size */
		SS->pipebuf = (void*)realloc(SS->pipebuf,SS->pipebufspace);
		if (! SS->pipebuf) zmalloc_failure = 1;
	      }
	      if (SS->pipebuf != eof) {
		/* Block changed.. Reset those pointers */
		long offsetchange = SS->pipebuf - eof;
		eol += offsetchange;
		s   += offsetchange;
	      }
	      memcpy(SS->pipebuf + SS->pipebufsize, buf, len);
	      SS->pipebufsize += len;
	      goto rescan_line;
	    }
	  } /* -- endif -- ... globbing more input */

	  p = eol-1;		  /* The '\n' at the end of the line	*/
	  if (p > s && p[-1] == '\r') --p; /* "\r\n" ?			*/
	  *p = 0;

	  if (SS->within_ehlo)
	    ehlo_check(SS, s+4);
	  if (!SS->esmtp_on_banner && SS->esmtp_on_banner > -2)
	    esmtp_banner_check(SS, s+4);

	  if (logfp)
	    fprintf(logfp, "%sr\t%s\n", logtag(), s);

	  if (SS->verboselog)
	    fprintf(SS->verboselog,"%s\n",s);

	  if (s[0] >= '0' && s[0] <= '9' &&
	      s[1] >= '0' && s[1] <= '9' &&
	      s[2] >= '0' && s[2] <= '9' &&
	      (s[3] == ' ' || s[3] == 0)) {
	    code = atoi(s);

	    /* We have a 'terminal' line */

	    SS->continuation_line = 0;
	  } else { /* it is 'continuation line', or some such, ignore */
	    SS->continuation_line = 1;
	  }

	  statesave = SS->cmdstate;

	  SS->cmdstate = SS->pipestates[idx];
	  if (idx == 0 && SS->first_line)
	    SS->prevcmdstate = SMTPSTATE99;

	  if (SS->first_line)
	    rmsgappend(SS, 0, "\r<<- %s",
		       SS->pipecmds[idx] ? SS->pipecmds[idx] : "(connecting)");

	  /* first_line is not exactly a complement of continuation_line,
	     it is rather a more complex entity. */

	  SS->first_line = !SS->continuation_line;

	  rmsgappend(SS, 1, "\r->> %s", s);

	  SS->cmdstate = statesave;


	  if (SS->continuation_line)
	    goto rescan_line_0;
	  else
	    SS->pipereplies = nextidx; /* Final line, mark this as processed! */
   

	  /* If write-fd has closed(shut down), we shall turn all
	     500-series hard errors into soft ones, as we must try
	     re-sending the message sometime. */

	  if ((SS->smtpfp == NULL || sffileno(SS->smtpfp) < 0) && code >= 500)
	    code -= 100; /* SOFTEN IT! */

	  rc = code_to_status(code, &status);

	  notarystatsave(SS,s,status);

	  if (SS->verboselog)
	     fprintf(SS->verboselog,
	     " lmtp_mode=%d code=%d rc=%d idx=%d datarp=%p pipercpts[idx]=%p pipecmds[idx]='%s'\n",
	     lmtp_mode, code, rc, idx, datarp, SS->pipercpts[idx],
	     SS->pipecmds[idx] ? SS->pipecmds[idx] : "<nil>");

	  if (SS->rcptstates & (FROMSTATE_500|HELOSTATE_500)) {
	    /* If "MAIL From:<..>" tells non-200 report, and
	       causes "RCPT To:<..>" commands to yield "400/500",
	       we IGNORE the "500" status. */
	    rc = EX_UNAVAILABLE;
	  } else if (SS->rcptstates & (FROMSTATE_400|HELOSTATE_400)) {
	    /* If "MAIL From:<..>" tells non-200 report, and
	       causes "RCPT To:<..>" commands to yield "400/500",
	       we IGNORE the "500" status. */
	    SS->rcptstates |= RCPTSTATE_400;
	    rc = EX_TEMPFAIL;
	  }

	  if (code >= 400) {
	    /* Errors */

	    /* MAIL From:<*>: 250/ 552/451/452/ 500/501/421 */
	    /* DATA: 354/ 451/554/ 500/501/503/421 */
	    /* RCPT To:<*>: 250/251/ 550/551/552/553/450/451/452/455/ 500/501/503/421 */

	    if (SS->pipercpts[idx] != NULL) {

	      if (code >= 500)
		SS->rcptstates |= RCPTSTATE_500;
	      else
		SS->rcptstates |= RCPTSTATE_400;
	      /* ``rc'' is correct. */

	      /* Diagnose the errors, we report successes AFTER the DATA phase.. */
	      /*
	      if (SS->verboselog)
		fprintf(SS->verboselog,
			" -> diagnostic(rc=%d idx=%d) remotemsg='%s'\n",
			rc, idx, SS->remotemsg);
	      */

	      time(&endtime);
	      notary_setxdelay((int)(endtime-starttime));
	      notaryreport(SS->pipercpts[idx]->addr->user,FAILED,NULL,NULL);

	      diagnostic(SS->verboselog, SS->pipercpts[idx], rc, 0, "%s", SS->remotemsg);
	      SMTP_MIB_diag(rc);
	      if (logfp) {
		fprintf(logfp, "%s#\t", logtag());
		diagnostic(logfp, SS->pipercpts[idx], rc, 0, "%s", SS->remotemsg);
	      }

	    } else { /* SS->pipercpts[idx] == NULL
			--> Connect, HELO, MAIL FROM or DATA/BDAT */

	      /* No diagnostic() calls for  MAIL FROM:<>, nor for
		 DATA/BDAT phases (except in LMTP mode) */

	      /*
	      if (SS->verboselog)
		fprintf(SS->verboselog,
			" -> diagnostic(rc=%d idx=%d) remotemsg='%s'\n",
			rc, idx, SS->remotemsg);
	      */


	      if ((idx == 0) && (SS->pipecmds[idx] != NULL) &&
		  (STREQN(SS->pipecmds[idx],"MAIL", 4))) {
		/* We are working on MAIL From:<...> command here */

		if (code >= 500)
		  SS->rcptstates |= FROMSTATE_500;
		else if (code >= 400)
		  SS->rcptstates |= FROMSTATE_400;
		else
		  SS->rcptstates |= FROMSTATE_OK;

	      } else {

		/* "DATA" or "BDAT" phase */

		if (lmtp_mode && datarp) {
		  /* LMTP is different animal..  We do  diagnostic() for all
		     recipients who have been reported as RCPTSTATE_OK */

		  notary_setxdelay((int)(endtime-starttime));
		  notaryreport(datarp->addr->user, FAILED, NULL, NULL);
		  diagnostic(SS->verboselog, datarp, rc, 0, "%s", SS->remotemsg);
		  SMTP_MIB_diag(rc);
		  if (logfp) {
		    fprintf(logfp, "%s#\t", logtag());
		    diagnostic(logfp, datarp, rc, 0, "%s", SS->remotemsg);
		  }
		  SS->rcptstates |= ((code >= 500) ?
				     RCPTSTATE_500 : RCPTSTATE_400);

		} /* LMTP mode */

		if (code >= 500) {
		  if (SS->rcptstates & (FROMSTATE_400|FROMSTATE_500)) {
		    /* The FROM failed already, make us 'soft' */
		    SS->rcptstates |= DATASTATE_400;
		  } else if (SS->rcptstates & RCPTSTATE_OK) {
		    /* At least one OK result for RCPTs,
		       It means we are REALLY hard error! */
		    SS->rcptstates |= DATASTATE_500;
		  } else if (SS->rcptstates & RCPTSTATE_400) {
		    /* TMPFAIL RCPTs, make us 'soft' error! */
		    SS->rcptstates |= DATASTATE_400;
		  } else {
		    /* All others are HARD errors! */
		    SS->rcptstates |= DATASTATE_500;
		  }
		} else if (code >= 400) {
		  SS->rcptstates |= DATASTATE_400;
		}
	      }

	    } /* SS->pipercpts[idx] == NULL */

	  } else { /* code < 400 */

	    /* Ok results */

	    if (SS->pipercpts[idx] != NULL) {
	      if (SS->rcptstates & (FROMSTATE_400|FROMSTATE_500)) {
		/* MAIL FROM gave error, we won't believe OK on
		   recipients either. */
		SS->rcptstates |= RCPTSTATE_400;
		/* Actually we SHOULD NOT arrive here, but we never know,
		   what kind of smtp-servers are out there... */
	      } else {
		/* MAIL FROM was apparently ok. */
		SS->rcptstates |= RCPTSTATE_OK;
		SS->pipercpts[idx]->status = EX_OK;
if (SS->verboselog) fprintf(SS->verboselog,"[Some OK - code=%d, idx=%d, pipeindex=%d]\n",code,idx,SS->pipeindex-1);
	      }
	    } else { /* MAIL FROM or DATA/BDAT */

	      if (idx == 0)
		SS->rcptstates |= FROMSTATE_OK;

	      /* DATA/BDAT phase */
	      if (lmtp_mode && datarp) {
		/* LMTP is different animal..  We do  diagnostic() for all
		   recipients who have been reported as RCPTSTATE_OK */
		time(&endtime);
		notary_setxdelay((int)(endtime-starttime));
		notaryreport(datarp->addr->user, "delivered", NULL, NULL);
		diagnostic(SS->verboselog, datarp, rc, 0, "%s", SS->remotemsg);
		SMTP_MIB_diag(rc);
		if (logfp) {
		  fprintf(logfp, "%s#\t", logtag());
		  diagnostic(logfp, datarp, rc, 0, "%s", SS->remotemsg);
		}
		SS->rcptstates |= RCPTSTATE_OK;

		if (SS->verboselog)
		  fprintf(SS->verboselog, " LMTP diagnostic() done; rc=%d code=%d datarp->lockoffset=%d%s\n", rc, code, datarp->lockoffset, datarp->lockoffset ? " **NOT ZERO!**":"");
	      } /* LMTP mode */

	      if (idx > 0) {
		if (SS->rcptstates & RCPTSTATE_OK)
		  SS->rcptstates |= DATASTATE_OK;
	      }
	    }
	  } /* end if 'code' interpretation */

	  /* Now compress away that processed dataset */
	  if (eol > SS->pipebuf) {
	    int sz = eol - SS->pipebuf;
	    SS->pipebufsize -= sz;
	    if (SS->pipebufsize > 0)
	      memmove(SS->pipebuf, eol, SS->pipebufsize);
	    s   = SS->pipebuf;
	    eol = SS->pipebuf;
	  }

	} /* for(..; idx < SS->pipeindex ; ..) */

	rc = EX_OK;
	if (rc == EX_OK && (SS->rcptstates & FROMSTATE_500))
	  rc = EX_UNAVAILABLE; /* MAIL FROM was a 5** code */
	if (rc == EX_OK && (SS->rcptstates & FROMSTATE_400))
	  rc = EX_TEMPFAIL; /* MAIL FROM was a 4** code */
	if (rc == EX_OK && err != 0)
	  rc = EX_TEMPFAIL; /* Some timeout happened at the response read */
	if (rc == EX_OK) {
	  /* Study the RCPT STATES! */
	  if (SS->rcptstates & RCPTSTATE_OK) {
	    rc = EX_OK; /* SOME OK */
	  } else if (SS->rcptstates & RCPTSTATE_400) {
	    /* Some TEMPFAIL */
	    rc = EX_TEMPFAIL;
	  } else if (SS->rcptstates & RCPTSTATE_500) {
	    /* only full failures :-( */
	    rc = EX_UNAVAILABLE;
	  }
	}
	if (rc == EX_OK) {
	  /* Study the DATA STATES! */
	  if (SS->rcptstates & DATASTATE_500)
	    rc = EX_UNAVAILABLE; /* All hard failures */
	  else if (SS->rcptstates & DATASTATE_400)
	    rc = EX_TEMPFAIL; /* Some TEMPFAIL */
#if 0
	  else if (SS->rcptstates & DATASTATE_OK)
	    rc = EX_OK; /* Some ok! */
#endif
	}

	if (rc != EX_OK && logfp)
	    fprintf(logfp,"%s#\t smtp_sync() did yield code %d/%s\n", logtag(), rc, sysexitstr(rc));
	if (SS->verboselog)
	  fprintf(SS->verboselog," smtp_sync() did yield code %d/%s (rcptstates = 0x%x)\n", rc, sysexitstr(rc), SS->rcptstates);

	return rc;
}

/* */
int
pipeblockread(SS)
SmtpState *SS;
{
	int infd = SS->smtpfd;
	char buf[512];
	int rc = EX_OK;

	/* BLOCKALARM; */
	if (SS->block_written && has_readable(infd)) {
	  /* Read and buffer all so far accumulated responses.. */
	  for (;;) {
	    /* Do non-blocking */
	    int r = smtp_nbread(SS, buf, sizeof buf);
	    if (r <= 0) break; /* Nothing to read ? EOF ?! */
	    if (SS->pipebuf == NULL) {
	      SS->pipebufspace = 240;
	      SS->pipebufsize  = 0;
	    }
	    while (SS->pipebufspace < (SS->pipebufsize+r+2))
	      SS->pipebufspace <<= 1;

	    /* malloc(size) == realloc(NULL,size) */
	    SS->pipebuf = realloc(SS->pipebuf,SS->pipebufspace);
	    if (! SS->pipebuf) zmalloc_failure = 1;

	    if (SS->pipebuf)
	      memcpy(SS->pipebuf+SS->pipebufsize,buf,r);
	    SS->pipebufsize += r;
	    SS->block_written = 0; /* We drain the accumulated input here,
				      and can thus mark this draining
				      unneeded for a while. */
	  }
	  /* Continue the processing... */
	}
	if (SS->pipebufsize)
	  rc = smtp_sync(SS, EX_OK, 1); /* NON-BLOCKING! */
	/* ENABLEALARM; */
	return rc;
}


void
smtppipestowage(SS, strbuf, syncrp)
	SmtpState *SS;
	const char *strbuf;
	struct rcpt *syncrp;
{
	if (SS->pipespace <= SS->pipeindex + 2) {
	  SS->pipespace += 8;

	  /* realloc(NULL,size) == malloc(size) */

	  SS->pipecmds  = (char**)realloc((void*)SS->pipecmds,
					  SS->pipespace * sizeof(char*));
	  SS->pipercpts = (struct rcpt **)realloc((void*)SS->pipercpts,
						  SS->pipespace *
						  sizeof(struct rcpt*));
	  SS->pipestates  = (int*)realloc((void*)SS->pipestates,
					  SS->pipespace * sizeof(int));
	}

	SS->pipecmds  [SS->pipeindex] = strbuf ? strdup(strbuf) : NULL;
	SS->pipercpts [SS->pipeindex] = syncrp; /* RCPT or NULL */
	SS->pipestates[SS->pipeindex] = SS->cmdstate;
	SS->pipeindex += 1;
}

int
smtpwrite(SS, saverpt, strbuf, pipelining, syncrp)
	SmtpState *SS;
	int saverpt;
	const char *strbuf;
	int pipelining;
	struct rcpt *syncrp;
{
	char buf[8192];
	int r = EX_OK, r2 = EX_OK;
	volatile int err = 0;

	gotalarm = 0; /* smtp_sfwrite() may set it.. */

	smtppipestowage(SS, strbuf, syncrp);

	if (strbuf != NULL) {
	  int len = strlen(strbuf) + 2;

	  if (pipelining > 0) {
	    /* We are asynchronous! */
	    SS->smtp_outcount += len; /* Where will we grow to ? */

	    /* Read possible responses into response buffer.. */
	    r2 = pipeblockread(SS);
	    /* FIXME: If we are seeing some errors ??? */

	    memcpy(buf,strbuf,len-2);
	    memcpy(buf+len-2,"\r\n",2);

	    if (SS->verboselog)
	      fwrite(buf, 1, len, SS->verboselog);

	    if (SS->smtpfp && !sferror(SS->smtpfp))
	      r = sfwrite(SS->smtpfp, buf, len);
	    else
	      r = -1;
	    err = (r != len) || !SS->smtpfp || sferror(SS->smtpfp);

	    if (SS->smtp_outcount > SS->smtp_bufsize) {
	      SS->smtp_outcount -= SS->smtp_bufsize;
	      SS->block_written = 1;
	    }

	  } else {

	    /* We act synchronously */

	    memcpy(buf,strbuf,len-2);
	    memcpy(buf+len-2,"\r\n",2);

	    if (SS->verboselog)
	      fwrite(buf, 1, len, SS->verboselog);

	    if (SS->smtpfp && !sferror(SS->smtpfp))
	      r = sfwrite(SS->smtpfp, buf, len);
	    else
	      r = -1;
	    err = (r != len);
	    if (!SS->smtpfp || sferror(SS->smtpfp) || sfsync(SS->smtpfp))
	      err = 1;

	  }

	  SS->lastactiontime = time(NULL);

	  if (err) {
	    if (gotalarm) {
	      strcpy(SS->remotemsg, "Timeout on cmd write");
	      time(&endtime);
	      notary_setxdelay((int)(endtime-starttime));
	      notaryreport(NULL,FAILED,"5.4.2 (timeout on cmd write)",
			   "smtp; 500 (timeout on cmd write)");
	    } else {
	      char *se = strerror(errno);
	      sprintf(SS->remotemsg, "smtp; 500 (write to server error: %s)", se);
	      time(&endtime);
	      notary_setxdelay((int)(endtime-starttime));
	      notaryreport(NULL,FAILED,"5.4.2 (write to server, err)",SS->remotemsg);
	    }
	    if (SS->verboselog)
	      fprintf(SS->verboselog,"%s\n",SS->remotemsg);
#if 0
	    smtpclose(SS, 1);
	    if (logfp)
	      fprintf(logfp, "%s#\t(closed SMTP channel - timeout on smtpwrite())\n", logtag());
	    /* Alarm OFF */
	    r = EX_TEMPFAIL;
#endif
	  } else if (r != len) {
	    sprintf(SS->remotemsg, "smtp; 500 (SMTP cmd write failure: Only wrote %d of %d bytes!)", r, len);
	    time(&endtime);
	    notary_setxdelay((int)(endtime-starttime));
	    notaryreport(NULL,FAILED,"5.4.2 (SMTP cmd partial write failure)",SS->remotemsg);
	    if (SS->verboselog)
	      fprintf(SS->verboselog,"%s\n",SS->remotemsg);
#if 0
	    smtpclose(SS, 1);
	    if (logfp)
	      fprintf(logfp, "%s#\t(closed SMTP channel - second timeout on smtpwrite() )\n", logtag());
	    /* Alarm OFF */
	    r = EX_TEMPFAIL;
#endif
	  }
	  if (logfp)
	    fprintf(logfp, "%sw\t%s\n", logtag(), strbuf);
	  if (err)
	    r = EX_TEMPFAIL;
	  else
	    r = EX_OK;
	}

	if (SS->smtpfp && sffileno(SS->smtpfp) >= 0) {
	  if (strbuf) {
	    rmsgappend(SS, 0, "\r<<- %s", strbuf);
	  } else {
	    SS->remotemsg[0] = 0;
	    rmsgappend(SS, 0, "\r<<- (null)");
	  }
	} else if (strbuf != NULL) {
	  /* socket closed outwards, commands not written! */
	  if (strbuf)
	    rmsgappend(SS, 0, "\rWrite Failure; shunted cmd: %s", strbuf);
	  else
	    strcpy(SS->remotemsg,
		   "\rWrite Failure; expecting initial greeting??");
	}

	/* ------------------------------------------------ */
	/* _________  Now begins reply collection _________ */

	if (pipelining) {
	  /* With "QUIT" this is negative value, and we are
	     not in reality interested of the return value... */

	  /* Read possible responses into response buffer.. */
	  r2 = pipeblockread(SS);
	  if (r != EX_OK) return r;
	  return r2;
	}

	return smtp_sync(SS, r, pipelining);
}


int
smtp_ehlo(SS, strbuf)
	SmtpState *SS;
	const char *strbuf;
{
	int rc;
	SS->within_ehlo = (SS->esmtp_on_banner > -2);
	SS->ehlo_capabilities = 0;
	SS->rcptstates = 0;
	rc = smtpwrite(SS, 1, strbuf, 0, NULL);
	SS->within_ehlo = 0;
	return rc;
}

/*
 * In theory, this should modify the command that ps shows for this process.
 * This is known not to be portable, hopefully it will break badly on systems
 * where it doesn't work.
 */

#ifdef HAVE_STDARG_H
#ifdef __STDC__
void report(SmtpState *SS, char *fmt, ...)
#else /* Not ANSI-C */
void report(SS, fmt)
	SmtpState *SS;
	char *fmt;
#endif
#else
/* VARARGS */
void
report(va_alist)
	va_dcl
#endif
{
	va_list	ap;
	char buf[8192];
	int cmdlen;

#ifdef HAVE_STDARG_H
	va_start(ap,fmt);
#else
	SmtpState *SS;
	char *fmt;
	va_start(ap);
	SS  = va_arg(ap, SmtpState *);
	fmt = va_arg(ap, char *);
#endif
	memset(buf, 0, sizeof(buf));

	if (SS->smtpfp && sffileno(SS->smtpfp) >= 0)
	  sprintf(buf, ">%.30s %.30s", SS->ipaddress, SS->sel_host ? SS->sel_host : "(nil)");
	else
	  sprintf(buf, ">[%.30s] %.30s ", SS->ipaddress, SS->sel_host ? SS->sel_host : "(nil)");
#ifdef	notdef
	if (logfp)
	  sprintf(buf+strlen(buf), ">>%s ", logfile);
	strcat(buf, "# ");
#endif
#ifdef	HAVE_VPRINTF
	vsprintf(buf+strlen(buf), fmt, ap);
#else	/* !HAVE_VPRINTF */
	sprintf(buf+strlen(buf), fmt, va_arg(ap, char *));
#endif	/* HAVE_VPRINTF */

#ifdef HAVE_SETPROCTITLE
	setproctitle("%s", buf);
#else
	cmdlen = (eocmdline - cmdline);
	if (cmdlen >= sizeof(buf))
	  cmdlen = sizeof(buf) - 1;
	for (fmt = buf+strlen(buf); fmt < buf + cmdlen; ++fmt)
	  *fmt = '\0';
	buf[cmdlen] = '\0';
	memcpy((char*)cmdline, buf, cmdlen); /* Overwrite it! */
#endif
	va_end(ap);
}

#ifdef	BIND

/*
 * This is the callback function for ctlopen.  It should return 0 to reject
 * an address, and 1 to accept it.  This routine will only be used if we've
 * been asked to check MX RR's for all hosts for applicability. Therefore we
 * check whether the  ap->host  has an MX RR pointing at the host that we have
 * an SMTP connection open with.  Return 1 if it is so.
 */

int
rightmx(spec_host, ap, cbparam)
	const char *spec_host;
	const struct taddress *ap;
	const void	*cbparam;
{
	SmtpState *SS = (void*)cbparam;
	int	i, rc;
	char realname[1024];

	if (CISTREQ(spec_host, ap->host))
	  return 1;
	if (SS->remotehost[0] == '\0')
	  return 0;

	memset(SS->mxh, 0, sizeof(SS->mxh));
	SS->mxh[0].host = NULL;
	SS->mxcount = 0;
	SS->firstmx = 0;

	if (statusreport)
	  report(SS,"MX-lookup: %s", ap->host);

	realname[0] = 0;
	switch (getmxrr(SS, ap->host, SS->mxh, MAXFORWARDERS, 0, realname, sizeof(realname), NULL)) {
	case EX_OK:
	  if (SS->mxh[0].host == NULL)
	    return CISTREQ(ap->host, SS->remotehost);
	  break;
	default:
	  return 0;
	}
	rc = 0;
	for (i = 0; SS->mxh[i].host != NULL; ++i) {
	  if (CISTREQ((const void*)SS->mxh[i].host, SS->remotehost))
	    rc = 1;
	  freeaddrinfo(SS->mxh[i].ai);
	  SS->mxh[i].ai = NULL;
	  free(SS->mxh[i].host);
	  SS->mxh[i].host = NULL;
	}
	return 0;
}


/* Hook for possible future implementation of a tricky thing
   to tell to the *scheduler*, what MXes each destination domain
   has, so that the scheduler could combine alike looking
   MX serviced destination domains together... */

void
mxsetsave(SS, host)
     SmtpState *SS;
     const char *host;
{
}

#endif	/* BIND */



void
notarystatsave(SS,smtpline,status)
SmtpState *SS;
char *smtpline, *status;
{
	char statbuf[10];
	int len = strlen(smtpline)+8+6;
#ifdef USE_ALLOCA
	char *str = alloca(len);
#else
	char *str = malloc(len);
#endif
	char *s = str;
#if 0
if (SS->verboselog)
  fprintf(SS->verboselog," notarystatsave1(len=%d status='%s', smtpline='%s')\n",len,status,smtpline);
#endif

	*statbuf = 0;
	strcpy(s,"smtp; ");
	s += 6;

	*s++ = *smtpline++;
	*s++ = *smtpline++;
	*s++ = *smtpline++;
	*s++ = ' ';
	if (*smtpline == ' ') ++smtpline;

	if (len >= 11) {
	  if (ESMTP_ENHSTATUS & SS->ehlo_capabilities) {
	    char *p = statbuf;
	    status = statbuf;
	    while ((p - statbuf) < sizeof(statbuf)-1) {
	      int c = (*smtpline) & 0xFF;
	      if (('0' <= c && c <= '9') || c == '.')
		*p++ = c;
	      else
		break;
	      ++smtpline;
	    }
	    *p = 0;
	    while (*smtpline == ' ' || *smtpline == '\t')
	      ++smtpline;
	  }
	}

	if (*smtpline) {
	  *s++ = '(';
	  while (*smtpline) {
	    switch (*smtpline) {
	    case '(':
	      *s++ = '[';
	      break;
	    case ')':
	      *s++ = ']';
	      break;
	    default:
	      *s++ = *smtpline;
	    }
	    ++smtpline;
	  }
	  *s++ = ')';
	}
	*s = 0;

	notaryreport(NULL,NULL,status,str);
#if 0
if (SS->verboselog)
  fprintf(SS->verboselog," notarystatsave2(status='%s', smtpline='%s')\n",status,str);
#endif
#ifndef USE_ALLOCA
	free(str);
#endif
}


void getdaemon()
{
	struct Zpasswd *pw = zgetpwnam("daemon");
	if (!pw) pw = zgetpwnam("daemons"); /* Some SGI machines! */
	if (!pw) pw = zgetpwnam("uucp");

	if (!pw) daemon_uid = 0; /* Let it be root, if nothing else */
	else     daemon_uid = pw->pw_uid;
}


/*  
 .. */


#ifndef SOL_TCP 	/* Latter Linuxes have SOL_TCP,
			   Solaris IPPROTO_TCP ..       */
# define SOL_TCP IPPROTO_TCP
#endif

static void tcpstream_nagle(fd)
     int fd;
{
	int i, r;
	if (fd < 0) return;

#ifdef TCP_CORK		/* Linux 2.4 / FreeBSD 5.x ?	*/
	i = 1;
	r = setsockopt(fd, SOL_TCP, TCP_CORK, (const void *)&i, sizeof(i));
#else
#ifdef TCP_NOPUSH	/* FreeBSD -- relates to T/TCP	*/
	i = 1;
	r = setsockopt(fd, SOL_TCP, TCP_NOPUSH, (const void *)&i, sizeof(i));
#else
#ifdef TCP_NODELAY	/* old original BSD network stack thing */
	i = 0;
	r = setsockopt(fd, SOL_TCP, TCP_NODELAY, (const void *)&i, sizeof(i));
#else
	/* No method at hand if none of above.. */
	i = r = 0; /* silense the compiler */
#endif
#endif
#endif
}

static void tcpstream_denagle(fd)
     int fd;
{
	int i, r;
	if (fd < 0) return;

#ifdef TCP_CORK
	i = 0;
	r = setsockopt(fd, SOL_TCP, TCP_CORK, (const void *)&i, sizeof(i));
	if (r < 0)
	  sleep(1); /* Fall back to classic timeout based anti-nagle.. */
#else
#ifdef TCP_NOPUSH
	i = 0;
	r = setsockopt(fd, SOL_TCP, TCP_NOPUSH, (const void *)&i, sizeof(i));
#if 0	/* original sendmail didn't have any code for this, actually */
	if (r < 0)
	  sleep(1); /* Fall back to classic timeout based anti-nagle.. */
#endif
#else
#ifdef TCP_NODELAY
	i = 1;		/* Turning this on DOES NOT FLUSH accumulated
			   data immediately!  Unlike TCP_CORK at Linux.. */
	r = setsockopt(fd, SOL_TCP, TCP_NODELAY, (const void *)&i, sizeof(i));
#if 0	/* original sendmail didn't have any code for this, actually */
	if (r < 0)
	  sleep(1); /* Fall back to classic timeout based anti-nagle.. */
#endif
#else
	i = r = 0;
#if 0	/* original sendmail didn't have any code for this, actually */
	sleep(1); /* Fall back to classic timeout based anti-nagle.. */
#endif
#endif
#endif
#endif
#if 0	/* In BSD (and Linux) systems we can ask what the outgoing
	   queue size is -- not so at Solaris ? */
	while (ioctl(fd, SIOCOUTQ, &count) == 0 && count != 0) {
	  if (poll(1, {fd, POLLIN}, 200))
	    abort_on_protocol_violation;
	  if ((tmo += 200) > long_timeo)
	    abort_on_stuck_connection;
	}                                                                 
#endif
}


/* ------------------------------------------------------------------
 * 
 *        CNAME caused translations; cache..
 *
 * ------------------------------------------------------------------ */

struct cnamecache_struct {
  int hash;
  int next;
  time_t ttl;
  const char *name;
  const char *cname;
};

#define CNAMECACHESIZE 1000

static int cnamecache_head;
static int cnamecache_free;
static struct cnamecache_struct  *cnamecache, *cp; /* BSS NULL value */

static void cnamecache_init __((FILE *verboselog));
static void cnamecache_init(verboselog)
     FILE *verboselog;
{
  int i;
  cnamecache = malloc(sizeof(struct cnamecache_struct) * CNAMECACHESIZE);
  if (!cnamecache) return; /* Urgh... */

  for (i = 0; i < CNAMECACHESIZE; ++i) {
    cp = & cnamecache[i];
    cp->next = i+1;
    cp->hash = cp->ttl   = 0;
    cp->name = cp->cname = NULL;
  }
  cnamecache[CNAMECACHESIZE-1].next = -1;
  cnamecache_free = 0;
  cnamecache_head = -1;

  /* if (verboselog) fprintf(verboselog,"CNAMEcache init() done\n"); */

}

static int namehash __((const char *));
static int namehash(s)
     const char *s;
{
  int hash = 0;
  for ( ; *s ; ++s) {
    unsigned char c = *s;
    if ('A' <= c && c <= 'Z') c += ('a' - 'A');
    hash += c;
  }
  return hash;
}


static int cname_lookup(SS, host, cnamep)
     SmtpState *SS;
     const char *host;
     const char ** cnamep;
{
  int hhash = namehash(host);
  int idx, nextidx;

  struct cnamecache_struct *ci, *cp;

  if (!cnamecache) cnamecache_init(SS->verboselog);
  if (!cnamecache) return -1; /* OOPS! */

  /* if (SS->verboselog) fprintf(SS->verboselog,"cname_lookup(name='%s'[%d])\n", host, hhash); */

  for ( idx = cnamecache_head, cp = NULL ;
	idx >= 0;
	cp = ci, idx = nextidx) {

    ci = & cnamecache[idx];
    nextidx = ci->next;

    if (ci->ttl < now) {
      /* Move this entry to FREE chain */
      if (cp) cp->next = ci->next;
      else /* When CP == NULL, we are at the FIRST cell, move head */
	cnamecache_head = ci->next;
      ci->next = cnamecache_free;
      cnamecache_free = idx;
      if (ci->name)  free((void*)(ci->name));   ci->name  = NULL;
      if (ci->cname) free((void*)(ci->cname));  ci->cname = NULL;
      ci = cp; /* Keep PREV pointer.. */
      continue;
    }

    if ((ci->hash == hhash) && ci->name && CISTREQ(ci->name, host)) {
      *cnamep = ci->cname;
      /* if (SS->verboselog) fprintf(SS->verboselog," ... found '%s'\n", ci->cname); */

      return 1;
    }
  }

  /* Not in cache.. */

  /* DNS LOOKUP! */
  {
    char realname[1024];
    time_t realnamettl;
    struct mxdata mxh[4];
    int rc, i;

    realname[0] = 0;
    realnamettl = 86400; /* Max cache age.. */
    memset( mxh, 0, sizeof(mxh) );

    /* if (SS->verboselog) fprintf(SS->verboselog," ... looking it up from DNS\n"); */

    rc = getmxrr(SS, host, mxh, 2, 0,
		 realname, sizeof(realname), &realnamettl);

    /* We did possibly collect up to two address entries, discard them here. */
    for (i = 0; i < 2; ++i) {
      if (mxh[i].host)  free(mxh[i].host);
      if (mxh[i].ai)    freeaddrinfo(mxh[i].ai);
    }

    realnamettl += now;

    if (rc == EX_OK) {
      mxsetsave(SS, host);
      *cnamep = add_cname_cache(SS, host, *realname ? realname : NULL, realnamettl);
      /* if (SS->verboselog) fprintf(SS->verboselog," ... returning successfully\n"); */

      return 1;
    }

  }

  /* if (SS->verboselog) fprintf(SS->verboselog," ... found nothing, not even from DNS.\n"); */

  return 0;
}

static const char *add_cname_cache(SS, host, cname, ttl)
     SmtpState *SS;
     const char *host, *cname;
     const time_t ttl;
{
  int hhash = namehash(host);
  int idx, nextidx;
  struct cnamecache_struct *ci, *cp;

  if (!cnamecache) cnamecache_init(SS->verboselog);
  if (!cnamecache) return NULL; /* OOPS! */

  /* if (SS->verboselog) fprintf(SS->verboselog,"add_cname_cache(host='%s', cname='%s', ttl= +%d)\n",host,cname?cname:"<NULL>",(int)(ttl-now)); */


  /* See if the table is full... */
  if (cnamecache_free < 0) {
    /* FULL!  We must blow a hole somewhere.. */
    /* .. anywhere! .. then main-loop finds an empty spot.  */
    cnamecache[ (rand() >> 12) % CNAMECACHESIZE ].ttl = now -1;
  }

  /* Check active list.. */
  for ( idx = cnamecache_head, cp = NULL ;
	idx >= 0 ;
	cp = ci, idx = nextidx) {

    ci = & cnamecache[idx];
    nextidx = ci->next;

    if (ci->ttl < now) {
      /* Move this entry to FREE chain */
      if (cp) cp->next = ci->next;
      else /* When CP == NULL, we are at the FIRST cell, move head */
	cnamecache_head = ci->next;
      ci->next = cnamecache_free;
      cnamecache_free = idx;
      if (ci->name)  free((void*)(ci->name));   ci->name  = NULL;
      if (ci->cname) free((void*)(ci->cname));  ci->cname = NULL;
      ci = cp; /* Keep PREV pointer.. */
      continue;
    }

    if (ci->hash == hhash && ci->name && CISTREQ(ci->name, host)) {
      if (ci->cname) free((void*)(ci->cname));  ci->cname = NULL;
      if (cname)  ci->cname = strdup(cname);
      /* if (SS->verboselog)fprintf(SS->verboselog," ... inserted into idx=%d\n",idx); */
      return ci->cname;
    }
  } /* thru active list */


  /* Pick first from the free chain: */
  idx = cnamecache_free;
  ci = & cnamecache[ idx ];
  cnamecache_free = ci->next;
  ci->next = cnamecache_head;
  cnamecache_head = idx;

  if (ci->name)  { free((void*)(ci->name));  }
  if (ci->cname) { free((void*)(ci->cname)); }
  if (cname)  ci->cname = strdup(cname); else ci->cname = NULL;
  ci->name = strdup(host);
  ci->hash = hhash;
  ci->ttl  = ttl;

  /*  if (SS->verboselog)fprintf(SS->verboselog," ... inserted into idx=%d\n",idx); */

  return ci->cname;
}

static void SMTP_MIB_diag(rc)
     const int rc;
{
  switch (rc) {
  case EX_OK:
    /* OK */
    MIBMtaEntry->tasmtp.TaRcptsOk ++;
    break;
  case EX_TEMPFAIL:
  case EX_IOERR:
  case EX_OSERR:
  case EX_CANTCREAT:
  case EX_SOFTWARE:
  case EX_DEFERALL:
    /* DEFER */
    MIBMtaEntry->tasmtp.TaRcptsRetry ++;
    break;
  case EX_NOPERM:
  case EX_PROTOCOL:
  case EX_USAGE:
  case EX_NOUSER:
  case EX_NOHOST:
  case EX_UNAVAILABLE:
  default:
    /* FAIL */
    MIBMtaEntry->tasmtp.TaRcptsFail ++;
    break;
  }
}
