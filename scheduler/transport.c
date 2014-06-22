/*
 *	Copyright 1988 by Rayan S. Zachariassen, all rights reserved.
 *	This will be free software, but only when it is finished.
 */
/*
 *	Lots of modifications (new guts, more or less..) by
 *	Matti Aarnio <mea@nic.funet.fi>  (copyright) 1992-2006
 */


#include "hostenv.h"
#include <sfio.h>
#include <sys/param.h>
#include "mail.h"
#ifdef HAVE_FCNTL_H
#include <fcntl.h>
#endif
#include <sys/stat.h>
#include <errno.h>
#include <sys/file.h>
#include "zmsignal.h"
/* #include <stdlib.h> */
#include <unistd.h>

#include "zsyslog.h"
#include <sysexits.h>
#ifdef HAVE_SYS_RESOURCE_H
#include <sys/resource.h> /* for setpriority */
#endif
#ifdef HAVE_SYS_UN_H
#include <sys/socket.h>
#include <sys/un.h>
#endif

#include "scheduler.h"
#include "prototypes.h"

#include "ta.h"
#include "libz.h"

#include "libc.h"
#include "zmpoll.h"

extern int forkrate_limit;
extern int freeze;
extern int mailqmode;

static int  scheduler_nofiles = -1; /* Will be filled below */
static int  runcommand   __((char * const argv[], char * const env[], struct vertex *, struct web *, struct web*));
static void stashprocess __((int, int, int, struct web*, struct web*, struct vertex *, char * const argv[]));
static void reclaim      __((int, int));
static void waitandclose __((int));
static void readfrom     __((int));

/* These two are *not* exactly proper ones, but at least at most
   systems it links properly without wider exportation of related
   data structure types.  */

extern int syncweb __((void *));
extern void *dirq;


extern FILE *vfp_open __((struct ctlfile *));

#ifdef HAVE_SYS_WAIT_H /* POSIX.1 compatible */
# include <sys/wait.h>
#else /* Not POSIX.1 compatible, lets fake it.. */
extern int wait();
#endif

#ifndef WEXITSTATUS
# define WEXITSTATUS(s) (((s) >> 8) & 0377)
#endif
#ifndef WSIGNALSTATUS
# define WSIGNALSTATUS(s) ((s) & 0177)
#endif

struct procinfo *cpids = NULL;

#define	MAXFILESPERTRANSPORT	1000

int	numkids;
int	readsockcnt;		/* Count how many childs to read there are;
				   this for the SLOW Shutdown */

int	notifysocket = -1;	/* fd of UDP/AF_UNIX socket to listen for notifies */


static void cmdbufalloc __((int, char **, int *));

static void
cmdbufalloc(newlen, bufp, spcp)
     int newlen;
     char **bufp;
     int *spcp;
{
  if (*bufp == NULL) {
    *bufp = emalloc(newlen+1);
    *spcp = newlen;
  }
  if (newlen > *spcp) {
    *bufp = erealloc(*bufp, newlen+1);
    *spcp = newlen;
  }
}

extern int errno;
extern int slow_shutdown;



/* 
 * Flush to child;
 * return -1 for failures and incomplete writes, 0 for success!
 */
static int  flush_child     __((struct procinfo *cpidp));

static int
flush_child(proc)
     struct procinfo *proc;
{

	if (proc->pid < 0 && proc->tofd >= 0) {
	  pipes_shutdown_child(proc->tofd);
	  proc->tofd = -1;

	  if (verbose)
	    sfprintf(sfstderr,
		     "%% shutdown of proc=%p pid=%d flush_child() pid<0 && tofd>=0\n",
		     proc, proc->pid);

	}
	if (proc->tofd < 0) {
	  proc->cmdlen = 0;
	  proc->state = CFSTATE_ERROR;

	  if (verbose)
	    sfprintf(sfstderr,
		     "%% disconnect of flush_child(proc=%p pid=%d) pid<0 && tofd<0 BAD?? \n",
		     proc, proc->pid);

	  return -1;
	}
#if 0
	/* Make sure the buffer exists.. */
	if (proc->cmdbuf == NULL)
	  cmdbufalloc(120, &proc->cmdbuf, &proc->cmdspc);
#endif
	if (proc->cmdlen == 0 && proc->tofd >= 0)
	  return 0; /* All done! */

	/* We have some leftovers from previous feed..
	   .. feed them now.  */

	/* sfprintf(sfstderr,
	   "flushing to child pid %d, cmdlen=%d, cmdbuf='%s'\n",
	   proc->pid, proc->cmdlen, proc->cmdbuf);  */

	while (proc->tofd >= 0 && proc->cmdlen > 0) {

	  int rc = write(proc->tofd, proc->cmdbuf, proc->cmdlen);

	  if (rc < 0 && (errno != EAGAIN && errno != EINTR &&
			 errno != EWOULDBLOCK)) {
	    int e = errno;
	    /* Some real failure :-( */
	    pipes_shutdown_child(proc->tofd);
	    proc->tofd = -1;
	    proc->cmdlen = 0;
	    proc->state = CFSTATE_ERROR;

	    if (verbose)
	      sfprintf(sfstderr,
		       "%% shutdown of proc=%p pid=%d flush_child() write() errno=%d\n",
		       proc, proc->pid, e);

	    return -1;
	  }
	  if (rc > 0) {
	    memcpy(proc->cmdbuf, proc->cmdbuf + rc, proc->cmdlen - rc);
	    proc->feedtime = now;
	  } else
	    break; /* Zero or negative.. let the writing
		      proceed later... */
	  proc->cmdlen -= rc;
	}
	if (proc->cmdlen) return 1; /* Incomplete write */
	return 0;
}


/*
 * The 'feed_child()' sends whatever is pointed by   proc->pthread->nextfeed;
 * return -1 for failures or "EOT", 1 for incomplete writes, 0 for success!
 */

static int  feed_child      __((struct procinfo *cpidp));

static int
feed_child(proc)
     struct procinfo *proc;
{
	struct vertex *vtx;
	int cmdlen;

	static char *cmdbuf = NULL;
	static int cmdbufspc = 0;

	if (proc->pthread == NULL) {
	  proc->state = CFSTATE_ERROR;
	  pipes_shutdown_child(proc->tofd);
	  proc->tofd = -1;

	  if (verbose)
	    sfprintf(sfstderr,
		     "%% shutdown of proc=%p pid=%d feed_child() proc->pthread == NULL\n",
		     proc, proc->pid);

	  return -1; /* BUG if called without next THREAD.. */
	}
	if (proc->pthread->nextfeed == NULL) {

	  if (verbose)
	    sfprintf(sfstderr,
		     "%% feed_child(proc=%p pid=%d) proc->pthread->nextfeed == NULL\n",
		     proc, proc->pid);

	  return -1; /* Might be called without next thing to process.. */
	}
	if (proc->pid <= 0 || proc->tofd < 0) {
	  proc->state = CFSTATE_ERROR;

	  if (verbose)
	    sfprintf(sfstderr,
		     "%% feed_child(proc=%p pid=%d tofd=%d) pid<0 || tofd<0 BAD??\n",
		     proc, proc->pid, proc->tofd);

	  return -1; /* No process../No write channel.. */
	}

	vtx = proc->pthread->nextfeed;

	mytime(&now);
#if 0
	if (vtx->lastfeed + 10 >= now)
	  return -1; /* Force at least 10 seconds in between feeds! */
#endif
	vtx->lastfeed = now;

	if (slow_shutdown) {

	  cmdlen = 1;
	  cmdbufalloc(cmdlen, & cmdbuf, & cmdbufspc);
	  strcpy(cmdbuf,"\n");

	} else {

	  const char *d = cfpdirname(vtx->cfp->dirind);
	  if (proc->thg->withhost) { /* cmd-line was with host */
	    cmdlen = 1 + strlen(d) + strlen(vtx->cfp->mid);
	    cmdbufalloc(cmdlen, & cmdbuf, & cmdbufspc);
	    sprintf(cmdbuf, "%s%s\n", d, vtx->cfp->mid);
	  } else {
	    cmdlen = 2+strlen(d)+strlen(vtx->cfp->mid)+strlen(proc->ho->name);
	    cmdbufalloc(cmdlen, & cmdbuf, & cmdbufspc);
	    sprintf(cmdbuf, "%s%s\t%s\n", d, vtx->cfp->mid, proc->ho->name);
	  }

	}

	if ((proc->cmdlen + cmdlen) >= proc->cmdspc)
	  cmdbufalloc(proc->cmdlen + cmdlen + 1, &proc->cmdbuf, &proc->cmdspc);

	/* Ok, copy it there.. */
	memcpy(proc->cmdbuf + proc->cmdlen, cmdbuf, cmdlen+1);
	proc->cmdlen += cmdlen;

	if (verbose) {
	  sfprintf(sfstdout,
		   "feed: tofd=%d, chan='%s', proc=%p, vtx=%p thr=%p ",
		   proc->tofd, proc->ch->name, proc, vtx, vtx->thread);
	}

	if (vtx->cfp->vfpfn != NULL) {
	  Sfio_t *vfp = vfp_open(vtx->cfp);
	  int i;
	  if (vfp) {
	    sfprintf(vfp, "Feeding to child; ce.argv = \"");
	    for (i = 0; vtx->thgrp->ce.argv[i] != NULL; ++i) {
	      if (i == 0)
		sfprintf(vfp, "'%s'", vtx->thgrp->ce.argv[i]);
	      else
		sfprintf(vfp, " '%s'", vtx->thgrp->ce.argv[i]);
	    }
	    sfprintf(vfp, "\" chan = '%s' cmd: %s", proc->ch->name, cmdbuf);
	    sfclose(vfp);
	  }
	}

	vtx->ce_pending  = 0; /* and clear the pending..       */
	/* DON'T double-count attempts on vertices!
	   This gets counted when some diagnostics is received for
	   this vertex. */
	/* vtx->attempts   += 1; */
	
	/* It was fed (to buffer), clear this flag.. */
	proc->overfed        += 1;
	proc->pthread->unfed -= 1;

	if (verbose)
	  sfprintf(sfstdout,"len=%d buf=%s", cmdlen, cmdbuf);

	mytime(&proc->feedtime);


	pick_next_vertex(proc);

	return flush_child(proc);
}


char *proc_state_names[] = {
  "ERROR", "LARVA", "STUFF", "FINISH", "IDLE"
};

void
ta_hungry(proc)
     struct procinfo *proc;
{
	/* This is an "actor model" behaviour,
	   where actor tells, when it needs a new
	   job to be fed to it. */

	struct thread *thr0;
	int i;

	mytime(&proc->hungertime);

	if (verbose)
	  sfprintf(sfstdout,"%% ta_hungry(%p) OF=%d S=%s tofd=%d\n",
		   proc, proc->overfed, proc_state_names[proc->state],
		   proc->tofd);

	/* If ``proc->tofd'' is negative, we can't feed anyway.. */

	if (proc->tofd < 0) {

	  --proc->overfed;

	  if (proc->overfed == 0 && proc->pthread)
	    /* If we have a thread here still, reschedule it... */
	    if (! thread_reschedule(proc->pthread,0,-1))
	      proc->pthread = NULL;

	  if (proc->pthread)
	    if (delete_thread(proc->pthread))
	      proc->pthread = NULL;

	  return;
	}

	/* We have valid child-feed state */

	proc->overfed -= 1;

	switch(proc->state) {
	case CFSTATE_LARVA: /* "1" */

	  /* Thread selected already along with its first vertex,
	     which is pointer by  proc->pthread->nextfeed  */

	  /* However if we have multiple parallel processes
	     in single thread, we may end up driving a new
	     process straight from LARVA to IDLE... */

	  proc->overfed = 0; /* Should not need setting ... */

	  if (proc->pthread->nextfeed != NULL &&
	      feed_child(proc) < 0)
	    /* We got some error :-/  D'uh! */
	    goto feed_error_handler;

	  proc->state = CFSTATE_STUFFING;
	  /* Not YET drained.. */
	  if (proc->pthread->nextfeed)
	    return;

	case CFSTATE_STUFFING: /* "2" */

	  if (proc->overfed > 0) return;

	  if (proc->pthread && proc->pthread->nextfeed) {

	    while ((proc->state == CFSTATE_STUFFING) &&
		   proc->pthread && proc->pthread->nextfeed) {

	      /* As long as:
		 - we have next vertex to feed
		 - there is no command buffer backlog
		 - state stays in STUFFING
	      */

	      i = feed_child(proc);
	      if (i < 0)
		goto feed_error_handler; /* Outch! */

	      if (proc->tofd >= 0 && proc->cmdlen != 0)
		break; /* Incomplete feed -- stop feeding here */

	      if (proc->overfed > proc->thg->ce.overfeed)
		break; /* Or over limit ...       */

	    }
	    /* As long as we have things to feed (or have fed anything!),
	       we stay in the STUFFING state.  This was if we later get
	       new workitems,  thread_linkin() can simply put them into
	       the 'nextfeed' pointer, and we feed them right away. */
	    return;
	  }

	  /* Didn't have anything to feed :-( */

	  proc->state = CFSTATE_FINISHING;
	  /* FALL THRU! */

	case CFSTATE_FINISHING: /* "3" */

	  /* "retryat" may have kicked us into this state also.. */

	  if (proc->overfed > 0) return;

	  /* Well, this thread was done, so long!
	     This TA may have other things to poke at! */

	  thr0 = proc->pthread;

	  /* proc->pthread = NULL; */
	  /* ^^^  NO KILL YET! pick_next_thread() needs this! */

	  /* Disconnect the previous thread from the proc. */

	  thr0->thrkids -= 1;

	  if (thr0->proc == proc) /* Thread Process Chain Leader */
	      thr0->proc = proc->pnext;

	  /* Disconnect from process chain */
	  if (proc->pnext) proc->pnext->pprev = proc->pprev;
	  if (proc->pprev) proc->pprev->pnext = proc->pnext;
	  proc->pnext = NULL;
	  proc->pprev = NULL;

	  /* Next: either the thread changes, or
	     the process moves into IDLE state. */

	  if (pick_next_thread(proc)) {

	    /* We have WORK !  We are reconnected to the new thread! */
	    /* Picked a new thread, which isn't same as THR0! */

	    /* Picked something, reschedule the old thread,
	       and if it got destroyed (by expiry) loose it... */
	    if (thr0 && !thread_reschedule(thr0, 0, -1))
	      thr0 = NULL;
	    if (thr0) delete_thread(thr0); /* possibly kill it if no more
					      things in it active! */
	    /* thr0 = NULL; -- this is dead variable.. */

	    if (verbose)
	      sfprintf(sfstdout, "%% pick_next_thread(proc=%p) gave thread %p\n",
		       proc, proc->pthread);

	    /* DON'T double-count attempts on threads!
	       This gets counted when some diagnostic is received
	       for this thing.. */
	    /* proc->pthread->attempts += 1; */

	    if (feed_child(proc))
	      /* non-zero return means things went wrong somehow.. */
	      goto feed_error_handler;

	    proc->state = CFSTATE_STUFFING;
	    return;
	  }

	  /* proc->pthread == NULL  now */
	  /* thr0->thrkids has been decremented */
	  /* No work in sight, queue up '#idle\n' string. */

	  if (thr0) {

	    /* Previously we were disconnected from the thread,
	     now join back to the head of the idle chain so that
	     IDLE processing will disconnect us... */

	    proc->pthread = thr0;
	    thr0->thrkids += 1;
	    proc->pnext   = thr0->proc;
	    if (proc->pnext) proc->pnext->pprev = proc;
	    proc->pprev   = NULL; /* already set */
	    thr0->proc = proc;
	  }

	  if ((proc->cmdlen + 7) >= proc->cmdspc) {
	    cmdbufalloc(proc->cmdlen+7, &proc->cmdbuf, &proc->cmdspc);
	  }
	  if (slow_shutdown) {
	    proc->cmdbuf[ proc->cmdlen ] = '\n';
	    proc->cmdlen += 1;
	  } else {
	    memcpy(proc->cmdbuf + proc->cmdlen, "#idle\n", 6);
	    proc->cmdlen += 6;
	  }
	  proc->state = CFSTATE_IDLE;
	  proc->overfed += 1;
	  flush_child(proc);  /* May flip the state to CFSTATE_ERROR */
	  return;

	case CFSTATE_IDLE: /* "4" */
	  /* The process has arrived into IDLE pool! */

	  if (proc->overfed > 0) abort();
	  /* We have seen at least once that this value went NEGATIVE! */

	  if (verbose)
	    sfprintf(sfstdout, " ... IDLE THE PROCESS %p (of=%d).\n",
		     proc, proc->overfed);

	  thr0 = proc->pthread;
	  if (thr0) {

	    proc->pthread = NULL;

	    if (thr0->proc == proc) /* Was chain head */
	      thr0->proc = proc->pnext;

	    thr0->thrkids -= 1;

	  }

	  /* Unlink me from the active chain */
	  if (proc->pnext) proc->pnext->pprev = proc->pprev;
	  if (proc->pprev) proc->pprev->pnext = proc->pnext;

	  proc->pnext = proc->thg->idleproc;
	  if (proc->pnext) proc->pnext->pprev = proc;
	  proc->pprev = NULL;
	  proc->thg->idleproc = proc;

	  proc->thg->idlecnt += 1;

	  ++idleprocs;
	  MIBMtaEntry->sc.TransportAgentsActiveSc -= 1;
	  MIBMtaEntry->sc.TransportAgentsIdleSc   += 1;


	  /* Failed to pick anything, reschedule the old thread.
	     Possibly killed the thread.. */
	  if (thr0) thread_reschedule(thr0, 0, -1);
	  return;

	default: /* CFSTATE_ERROR: "0" */
	  /* Some error was encountered at  feed_child()  at some
	     point, we do nothing! */

	  /* Some (real?) failure :-( */

	feed_error_handler:

	  if (verbose)
	    sfprintf(sfstdout,"%% ta_hungry(%p) OF=%d S=%s tofd=%d\n",
		     proc, proc->overfed, proc_state_names[proc->state],
		     proc->tofd);

	  proc->state = CFSTATE_ERROR;

	  /* We shut-down the child feed pipe */
	  pipes_shutdown_child(proc->tofd);
	  proc->tofd = -1;
	  break;
	}
	return;
}

/*
 * start_child() -- build argv[], and do other inits for fork()ing
 *                  and execve()ing a new transport program for us.
 */

int
start_child(vhead, chwp, howp)
	struct vertex *vhead;
	struct web *chwp, *howp;
{
#define MAXARGC 40
	char * av[1+MAXARGC];
	char * ev[1+MAXARGC];
	char *os, *cp, *ocp, *s;
	char buf[MAXPATHLEN*4];
	char buf2[MAXPATHLEN];

	int	 i, avi, evi;
	static time_t prev_time = 0;
	static int startcnt = 0; /* How many childs per second (time_t tick..) ? */
	time_t this_time;


	if (freeze) {
	  vhead->thread->pending = "Frozen";
	  return 0;
	}

	if (verbose)
	  sfprintf(sfstdout,"transport(vhead=%p,chan=%s,host=%s)\n",
		   vhead,chwp->name,howp->name);

	++startcnt;
	this_time = mytime(NULL);
	if (this_time != prev_time) {
	  startcnt = 0;
	  prev_time = this_time;
	} else if (startcnt > forkrate_limit) {
	  if (verbose)
	    sfprintf(sfstdout," ... too many forks per second!\n");
	  vhead->thread->pending = "ForkRateLimit";
	  return 0;
	}

	if (vhead->thgrp->ce.argv == NULL) {
	  sfprintf(sfstderr, "No command defined for %s/%s!\n",
		  chwp->name, howp->name);
	  vhead->thread->pending = "ConfBUG:NoCmdDefined!";
	  return 0;
	}

	/*
	 * Replace the $host and $channel strings in the command line.
	 * (also any ${ZENV} variable)
	 */
	os = buf;
	avi = evi = 0;
	for (i = 0; vhead->thgrp->ce.argv[i] != NULL; ++i) {
	  if (strcmp(vhead->thgrp->ce.argv[i], replhost) == 0) {
	    av[avi] = howp->name;
	  } else if (strcmp(vhead->thgrp->ce.argv[i], replchannel) == 0) {
	    av[avi] = chwp->name;
	  } else if (strchr(vhead->thgrp->ce.argv[i], '$') != NULL) {
	    s = os;
	    for (cp = vhead->thgrp->ce.argv[i]; *cp != '\0'; ++cp) {
	      if (*cp == '$' && *(cp+1) == '{') {
		cp += 2;
		ocp = cp;
		while (*cp != '\0' && *cp != '}')
		  ++cp;
		if (*cp == '}') {
		  *cp = '\0';
		  if (strcmp(ocp,"host")==0) {
		    strcpy(s,howp->name);
		  } else if (strcmp(ocp,"channel")==0) {
		    strcpy(s,chwp->name);
		  } else {
		    const char *t = getzenv(ocp);
		    if (t)
		      strcpy(s, t);
		  }
		  s += strlen(s);
		  *cp = '}';
		} else
		  --cp;
	      } else
		*s++ = *cp;
	    }
	    *s = '\0';
	    av[avi] = os;
	    os = s + 1;
	  } else
	    av[avi] = vhead->thgrp->ce.argv[i];

	  if (os >= (buf+sizeof(buf))) {
	    sfprintf(sfstderr,"BUFFER OVERFLOW IN ARGV[] SUBSTITUTIONS!\n");
	    sfsync(sfstderr);
	    abort();
	  }

	  if (avi == 0 && strchr(av[0],'=') != NULL) {
	    ev[evi] = av[0];
	    ++evi;
	  } else if (avi == 0 && av[0][0] != '/') {
	    /* Must add ${MAILBIN}/ta/ to be the prefix.. */

	    static const char *mailbin = NULL;

	    if (!mailbin) mailbin = getzenv("MAILBIN");
	    if (!mailbin) mailbin = MAILBIN;

	    sprintf(buf2,"%s/%s/%s", mailbin, qdefaultdir, av[0]);
	    av[avi++] = buf2;
	    if (strlen(buf2) > sizeof(buf2)) {
	      /* Buffer overflow ! This should not happen, but ... */
	      sfprintf(sfstderr,"BUFFER OVERFLOW IN ARGV[0] CONSTRUCTION!\n");
	      sfsync(sfstderr);
	      abort();
	    }
	  } else
	    ++avi;
	  if (avi >= MAXARGC) avi = MAXARGC;
	  if (evi >= MAXARGC) evi = MAXARGC;
	}
	av[avi] = NULL;
	{
	  const char *t;
	  if ((t = getenv("TZ")))
	    ev[evi++] = (char*) t-3; /* Pass the TZ      */
	  if ((t = getzenv("PATH")))
	    ev[evi++] = (char*) t-5; /* Pass the PATH    */
	  if ((t = getzenv("ZCONFIG")))
	    ev[evi++] = (char*) t-8; /* Pass the ZCONFIG */
	}
	ev[evi] = NULL;

	/* fork off the appropriate command with the appropriate stdin */
	if (verbose) {
	  sfprintf(sfstdout,"${");
	  for (i = 0; ev[i] != NULL; ++i)
	    sfprintf(sfstdout," %s", ev[i]);
	  sfprintf(sfstdout," }");
	  for (i = 0; av[i] != NULL; ++i)
	    sfprintf(sfstdout," %s", av[i]);
	  sfprintf(sfstdout,"\n");
	}
	return runcommand(av, ev, vhead, chwp, howp);
}

static int runcommand(argv, env, vhead, chwp, howp)
	char * const argv[];
	char * const env[];
	struct vertex *vhead;
	struct web *chwp, *howp;
{
	int	i, pid, to[2], from[2], uid, gid, prio;
	char	*cmd;
	static int pipesize = 0;


	uid = vhead->thgrp->ce.uid;
	gid = vhead->thgrp->ce.gid;
	cmd = argv[0];
	prio= vhead->thgrp->ce.priority;

	if (pipes_create(to,from) < 0) return 0;
	if (pipesize == 0)
	  pipesize = resources_query_pipesize(to[0]);

	if (verbose)
	  sfprintf(sfstderr, "to %d/%d from %d/%d\n",
		  to[0],to[1],from[0],from[1]);

	pid = fork();
	if (pid == 0) {	/* child */

	  pipes_to_child_fds(to,from);

	  /* keep current stderr for child stderr */
	  /* close all other open filedescriptors */

	  /* ... if detach() did its job, there shouldn't be any! */
	  /* ... no, the 'querysock' is there somewhere!   */
	  if (scheduler_nofiles < 1)
	    scheduler_nofiles = resources_query_nofiles();
	  for (i = 3; i < scheduler_nofiles; ++i)
	    close(i);

#if defined(HAVE_SETPRIORITY) && defined(HAVE_SYS_RESOURCE_H)
	  if (prio >= 80) { /* MAGIC LIMIT VALUE FOR ABSOLUTE SET! */
	    setpriority(PRIO_PROCESS, 0, i - 100);
	  } else
#endif
	    if (prio != 0) {
	      nice(prio);
	    }

	  resources_limit_nofiles(transportmaxnofiles);
	  setgid(gid);	/* Do GID setup while still UID 0..   */
	  setuid(uid);	/* Now discard all excessive powers.. */
	  execve(cmd, argv, env);
	  sfprintf(sfstderr, "Exec of %s failed!\n", cmd);
	  _exit(1);
	} else if (pid < 0) {	/* fork failed - yell and forget it */
	  close(to[0]); close(to[1]);
	  close(from[0]); close(from[1]);
	  sfprintf(sfstderr, "Fork failed!\n");
	  vhead->thread->pending = "System:ForkFailure!";
	  return 0;
	}

	/* parent */

	pipes_close_parent(to,from);

	/* save from[0] away as a descriptor to watch */
	stashprocess(pid, from[0], to[1], chwp, howp, vhead, argv);
	/* We wait for the child to report "#hungry", then we feed it.. */
	return 1;
}


static void stashprocess(pid, fromfd, tofd, chwp, howp, vhead, argv)
	int pid, fromfd, tofd;
	struct web *chwp, *howp;
	struct vertex *vhead;
	char * const argv[];
{
	int i, l, j;
	struct procinfo *proc;

	if (cpids == NULL) {
	  if (scheduler_nofiles < 1)
	    scheduler_nofiles = resources_query_nofiles();
	  i = scheduler_nofiles;
	  cpids = (struct procinfo *)
	    emalloc((unsigned)(i * sizeof (struct procinfo)));
	  memset(cpids, 0, sizeof(struct procinfo) * i);
	}
	proc = &cpids[fromfd];

	/* Free these buffers in case they exist from last use.. */
	if (proc->cmdbuf)  free(proc->cmdbuf);
	if (proc->cmdline) free(proc->cmdline);

	memset(proc,0,sizeof(struct procinfo));
#if 0 /* the memset() does this more efficiently.. */
	proc->pnext   = NULL;
	proc->pprev   = NULL;
	proc->cmdlen = 0;
	proc->reaped = 0;
	proc->carryover = NULL;
#endif

	proc->overfed = 1;
	proc->state   = CFSTATE_LARVA;

	proc->pid     = pid;

	proc->ch      = chwp;
	chwp->kids   += 1;

	proc->ho      = howp;
	howp->kids   += 1;

	proc->pthread            = vhead->thread;

	proc->thg           = vhead->thread->thgrp;
	proc->thg->transporters += 1;
	proc->pthread->thrkids  += 1;

	++numkids;
	MIBMtaEntry->sc.TransportAgentProcessesSc += 1;
	MIBMtaEntry->sc.TransportAgentForksSc     += 1;
	MIBMtaEntry->sc.TransportAgentsActiveSc   += 1;


	proc->tofd          = tofd;
	proc->pnext         = proc->pthread->proc;
	/* proc->pprev = NULL; */
	proc->pthread->proc = proc;
	if (proc->pnext) proc->pnext->pprev = proc;

	mytime(&proc->hungertime); /* Actually it is not yet 'hungry' as
				      per reporting so, but we store the
				      time-stamp anyway */

	cmdbufalloc(200, &proc->cmdbuf,  &proc->cmdspc);
	cmdbufalloc(200, &proc->cmdline, &proc->cmdlspc);

	fd_nonblockingmode(fromfd);
	if (fromfd != tofd)
	  fd_nonblockingmode(tofd);

	/* Construct a faximille of the argv[] in a single string.
	   This is entirely for debug porposes in some rare cases
	   where transport subprocess returns EX_SOFTWARE, and we
	   send out LOG_EMERG alerts thru syslog.  */
	proc->cmdline[0] = 0;
	l = 0;
	for (i = 0; argv[i] != NULL; ++i) {
	  if (i > 0)
	    proc->cmdline[l++] = ' ';
	  j = strlen(argv[i]);
	  cmdbufalloc(l+j+1, &proc->cmdline, &proc->cmdlspc);
	  memcpy(proc->cmdline+l, argv[i], j);
	  l += j;
	}
	proc->cmdline[l] = '\0';

	if (verbose)
	  sfprintf(sfstderr,
		   "stashprocess(%d, %d, %d, %s, %s, '%s' proc=%p)\n",
		   pid, fromfd, tofd, chwp ? chwp->name : "nil",
		   howp ? howp->name : "nil", proc->cmdline, proc);
}

/*
 * shutdown all kids that we have
 */
void
shutdown_kids()
{
	int i;
	struct procinfo *proc = cpids;

	if (!cpids) return; /* Nothing to do! */

	for (i = 0; i < scheduler_nofiles; ++i,++proc)
	  if (proc->pid > 0 && proc->tofd >= 0) {
	    /* Send the death-marker to the kid, and
	       then close the command channel */
	    write(proc->tofd,"\n\n",2);
	    pipes_shutdown_child(proc->tofd);
	    proc->tofd = -1;
	    /* Signals may happen... */
	    if (proc->pid > 1)
	      kill(proc->pid, SIGQUIT);
	  }
}

/* 
 *  Reclaim the process slot -- this process is dead now.
 */
static void reclaim(fromfd, tofd)
	int fromfd, tofd;
{
	struct procinfo *proc = &cpids[fromfd];

	if (verbose)
	  sfprintf(sfstderr,"reclaim(%d,%d) pid=%d, reaped=%d, chan=%s, host=%s\n",
		   fromfd, tofd, (int)proc->pid, proc->reaped,
		   proc->ch->name, proc->ho->name);

	if (proc->reaped &&
	    ((WIFEXITED(proc->waitstat) && WEXITSTATUS(proc->waitstat)) ||
	     WIFSIGNALED(proc->waitstat))) {

	  /* Child sig-faulted, or had non-zero exit status! */

	  sfprintf(sfstderr,
		   "reclaim(%d,%d) pid=%d, reaped=%d, chan=%s, host=%s ",
		   fromfd, tofd, (int)proc->pid, proc->reaped,
		   proc->ch->name, proc->ho->name);

	  if (WIFEXITED(proc->waitstat))
	    sfprintf(sfstderr,"EXIT=%d\n", WEXITSTATUS(proc->waitstat));
	  else if (WIFSIGNALED(proc->waitstat))
	    sfprintf(sfstderr,"SIGNAL=%d\n", WTERMSIG(proc->waitstat));
	  else
	    sfprintf(sfstderr,"WAITSTAT=0x%04x\n", proc->waitstat);
	}

	proc->pid = 0;
	proc->reaped = 0;
	if (proc->carryover != NULL) {
	  sfprintf(sfstderr, "%s: HELP! Lost %d bytes: '%s'\n",
		  progname, (int)strlen(proc->carryover), proc->carryover);
	  free(proc->carryover);
	  proc->carryover = NULL;
	}
	if (proc->ch) {
	  proc->ch->kids -= 1;
	  unweb(L_CHANNEL, proc->ch);
	  proc->ch = NULL;
	}
	if (proc->ho) {
	  proc->ho->kids -= 1;
	  unweb(L_HOST, proc->ho);
	  proc->ho = NULL;
	}
	if (tofd >= 0)
	  pipes_shutdown_child(tofd);
	close(fromfd);

	/* Reschedule the vertices that are left
	   (that were not reported on).		*/

	/* ... but only if we were not in IDLE chain! */
	if (proc->pthread) {

	  /* Remove this entry from the chains */

	  /* Chain leader */
	  if (proc->pthread->proc == proc) {
	    proc->pthread->proc = proc->pnext;
	  }
	  /* Following should have been done.. */
	  if (proc->pnext) proc->pnext->pprev = proc->pprev;
	  if (proc->pprev) proc->pprev->pnext = proc->pnext;
	  proc->pnext = NULL;
	  proc->pprev = NULL;

	  /* Disjoin the thread from the proc */
	  proc->pthread->thrkids -= 1;

	  /* Conditionally reschedule the thread */
	  thread_reschedule(proc->pthread,0,-1);

	  proc->pthread = NULL;

	} else {

	  /* Maybe we were in idle chain! */
	  struct procinfo *p;

	  p  =  proc->thg->idleproc;
	  while (p && p != proc) p = p->pnext;
	  if (p == proc) {
	    proc->thg->idlecnt -= 1;
	    --idleprocs;

	    /* Virtually move to ACTIVE state for count off below */
	    MIBMtaEntry->sc.TransportAgentsActiveSc += 1;
	    MIBMtaEntry->sc.TransportAgentsIdleSc   -= 1;

	    /* Remove this entry from the chains */
	    if (proc == proc->thg->idleproc)
	      proc->thg->idleproc = proc->pnext;
	  }
	}

	/* Remove this entry from the chains */
	if (proc->pnext) proc->pnext->pprev = proc->pprev;
	if (proc->pprev) proc->pprev->pnext = proc->pnext;
	proc->pnext = NULL;
	proc->pprev = NULL;

	/* If e.g. RESCHEDULE has not destroyed this thread-group.. */
	if (proc->thg) {
	  proc->thg->transporters -= 1;
	  /* It may go down to zero and be deleted.. */
	  delete_threadgroup(proc->thg);
	  proc->thg    = NULL;
	}

	MIBMtaEntry->sc.TransportAgentsActiveSc   -= 1;
	MIBMtaEntry->sc.TransportAgentProcessesSc -= 1;
	--numkids;
	proc->thg    = NULL;
}

static void waitandclose(fd)
	int	fd;
{
	/* This is called when
	   - fd return 0 (EOF)
	   - fd returns -1, and errno != {EAGAIN|EWOULDBLOCK|EINTR}
	 */
	reclaim(fd, cpids[fd].tofd);
}


int in_poll = 0;

int
mux(timeout)
time_t timeout;
{
	int	i, n;
	int wait_secs;
	struct procinfo *proc = cpids;

	int fdscount = 0;
	static struct zmpollfd *fds = NULL;

	struct zmpollfd *queryfds  = NULL;
	struct zmpollfd *query6fds = NULL;
	struct zmpollfd *notifyfds = NULL;

	timed_log_reinit();

	if (in_poll) {
	  sfprintf(sfstderr,"**** recursed into mux()! ***\n");
	  return 0;
	}

	queryipccheck();

	wait_secs = timeout - now; /* Timeout in seconds */
	if (timeout < now)
	  wait_secs = 0;

	fdscount = 0;
	readsockcnt = 0;
	if (cpids != NULL)
	  for (proc = cpids,i = 0; i < scheduler_nofiles ; ++i,++proc) {
	    proc->fdpfrom = proc->fdpto = NULL;

	    if (proc->pid != 0) {
	      /* Something can be read ? */
	      zmpoll_addfd(&fds, &fdscount, i, -1, &(proc->fdpfrom));
	      /* sfprintf(sfstderr,"**** QX zmpoll_addfd(fds, %d, %d, %d, fdpfrom) QX ***\n", fdscount, i, -1); */

	      ++readsockcnt;
	      /* Something to write ? */
	      if (proc->cmdlen > 0 && proc->tofd >= 0) {
	        zmpoll_addfd(&fds, &fdscount, -1,  proc->tofd, &(proc->fdpto));
	        /* sfprintf(sfstderr,"**** QX zmpoll_addfd(fds, %d, %d, %d, fdpto) QX ***\n", fdscount, -1, proc->tofd); */
	      } else {
		proc->fdpto = NULL;
	      }

	    }
	  }

	if (querysocket >= 0)
	  zmpoll_addfd(&fds, &fdscount, querysocket,  -1, &queryfds);

	if (querysocket6 >= 0)
	  zmpoll_addfd(&fds, &fdscount, querysocket6, -1, &query6fds);

	if (notifysocket >= 0)
	  zmpoll_addfd(&fds, &fdscount, notifysocket, -1, &notifyfds);

	/* Although we don't react on the results of these MQ2 fd's
	   here in main loop, getting them to break timeouts is
	   important for MAILQv2 responsiveness. ! */

	if (mailqmode == 2)
	  mq2add_to_poll(&fds, &fdscount);

	if (fdscount == 0) {
	  return -1;
	}

	/* sfprintf(sfstderr, "about to select on %x [%d]\n",
	   mask.fds_bits[0], maxf); */

	in_poll = 1;

	/* n = select(maxf, &rdmask, &wrmask, NULL, &tv); */
	n = zmpoll(fds, fdscount, wait_secs * 1000);
	if (verbose)
	  sfprintf(sfstderr,"**** QX zmpoll(fds, %d, %d * 1000) = %d; QX ***\n", fdscount, wait_secs, n);


	if (n < 0) {
	  int err = errno;

	  timed_log_reinit();

	  /* sfprintf(sfstderr, "got an interrupt (%d)\n", errno); */
	  in_poll = 0;
	  if (err == EINTR || err == EAGAIN) {
	    return 0;
	  }
	  if (err == EINVAL || err == EBADF) {
	    sfprintf(sfstderr, "** select() returned errno=%d\n", err);
	    for (i = 0; i < fdscount; ++i) {
	      if (fds[i].events & ZM_POLLIN && fcntl(fds[i].fd,F_GETFL,0) < 0)
		sfprintf(sfstderr,"** Invalid fd on a zmpoll() ZM_POLLIN fds: %d\n", fds[i].fd);
	      if (fds[i].events & ZM_POLLOUT && fcntl(fds[i].fd,F_GETFL,0) < 0)
		sfprintf(sfstderr,"** Invalid fd on a zmpoll() ZM_POLLOUT fds: %d\n", fds[i].fd);
	    }
	    sfsync(sfstderr);
	    abort(); /* mux() select() error EINVAL or EBADF !? */
	  }
	  perror("poll() returned unknown error ");
	  fflush(stderr);
	  sfsync(sfstderr);
#if 0
	  abort(); /* Select with unknown error */
#endif
	} else if (n == 0) {
	  /* sfprintf(sfstderr, "abnormal 0 return from select!\n"); */
	  /* -- just a timeout -- fast or long */
	  timed_log_reinit();
	  in_poll = 0;
	  return 1;
	} else {
	  /*sfprintf(sfstderr, "got %d ready (%x)\n", n, rdmask.fds_bits[0]);*/

	  /* In case we really should react.. */
	  if (querysocket >= 0 && queryfds &&
	      queryfds->revents & (ZM_POLLIN|ZM_POLLERR|ZM_POLLHUP))
	    queryipccheck();
	  if (querysocket6 >= 0 && query6fds &&
	      query6fds->revents & (ZM_POLLIN|ZM_POLLERR|ZM_POLLHUP))
	    queryipccheck();
	  
	  if (notifysocket >= 0 && notifyfds &&
	      notifyfds->revents & (ZM_POLLIN|ZM_POLLERR|ZM_POLLHUP))
	    receive_notify(notifysocket);

	  if (cpids != NULL) {

	    for (proc = cpids, i = 0; i < scheduler_nofiles; ++i, ++proc) {
	      /* sfprintf(sfstderr,"**** QX i = %d QX ***\n", i); */
	      
	      timed_log_reinit();

	      if (proc->pid < 0 ||
	          (proc->pid > 0 && proc->fdpfrom &&
		   proc->fdpfrom->revents & (ZM_POLLIN|ZM_POLLERR|ZM_POLLHUP))) {

		/* _Z_FD_CLR(i, rdmask); */
		/*sfprintf(sfstderr,"that is fd %d\n",i);*/
		/* do non-blocking reads from this fd */
		readfrom(i);
	      }

	      /* In case we have non-completed 'feeds', try feeding them */
	      if (proc->pid > 0    &&  proc->tofd >= 0   &&
		  proc->cmdlen > 0 &&
		  proc->fdpto && proc->fdpto->revents & ZM_POLLOUT)
		flush_child(proc);

	      /* Because this loop might take a while ... */
	      queryipccheck();

	      syncweb(dirq);

	    }
	  }

	  in_poll = 0;
	}
	/* sfprintf(sfstderr, "return from mux\n"); */
	return 0;
}



/* Call it how often you wish, but act it only once a second, or so.. */
static time_t lastqueryipccheck;
static time_t qipcretry;

void
queryipccheck()
{
	int	n;

	timed_log_reinit(); /* internal: mytime(&now); */

	if (!mq2_active() && (lastqueryipccheck == now)) return;
	lastqueryipccheck = now;

	if (qipcretry > 0 && qipcretry <= now) {
	  qipcretry = 0;
	  queryipcinit();
	  /*
	   * If qipcretry is set here, the value will be ignored, but
	   * that's ok since sweepretry is active by now
	   */
	}

	if ( (querysocket  >= 0) ||
	     (querysocket6 >= 0) ||
	     (notifysocket >= 0)    ) {

	  int fdscount;
	  struct zmpollfd *fds = NULL;

	  struct zmpollfd *queryfds = NULL;
	  struct zmpollfd *query6fds = NULL;
	  struct zmpollfd *notifyfds = NULL;

	  fdscount = 0;

	  if (querysocket >= 0)
	    zmpoll_addfd( &fds, &fdscount, querysocket,  -1, &queryfds);

	  if (querysocket6 >= 0)
	    zmpoll_addfd( &fds, &fdscount, querysocket6, -1, &query6fds);

	  if (notifysocket >= 0)
	    zmpoll_addfd( &fds, &fdscount, notifysocket, -1, &notifyfds);


	  if (mailqmode == 2) {
	    mq2add_to_poll(&fds, &fdscount);

	    n = zmpoll(fds, fdscount, /* wait: */ 0 /* ms */ );

	    if (n > 0)
	      mq2_areinsets(fds);

	  } else 
	    n = zmpoll(fds, fdscount, /* wait: */ 0 /* ms */ );

	  if (notifyfds &&
	      (notifyfds->revents & (ZM_POLLIN|ZM_POLLERR|ZM_POLLHUP)))
	    receive_notify(notifysocket);
	  if (notifyfds) notifyfds->revents = 0;

	  if (query6fds &&
	      (query6fds->revents & (ZM_POLLIN|ZM_POLLERR|ZM_POLLHUP))) {

	    Usockaddr raddr;
	    int raddrlen = sizeof(raddr);

	    n = accept(querysocket6, (struct sockaddr *)&raddr, (void*)&raddrlen);
	    if (n >= 0) {
	      if (mailqmode == 1) {
		int pid;

		MIBMtaEntry->sc.MQ1sockConnects ++;
		MIBMtaEntry->sc.MQ1sockParallel ++;

		pid = fork();
		if (pid == 0) {
#if defined(F_SETFD)
		  fcntl(n, F_SETFD, 1); /* close-on-exec */
#endif
#ifdef USE_TCPWRAPPER
#ifdef HAVE_TCPD_H /* TCP-Wrapper code */
		  if (wantconn(n, "mailq") == 0) {
		    char *msg = "500 TCP-WRAPPER refusing 'mailq' query from your whereabouts\r\n";
		    int   len = strlen(msg);
		    write(n,msg,len);
		    MIBMtaEntry->sc.MQ1sockParallel --;
		    MIBMtaEntry->sc.MQ1sockTcpWrapRej ++;
		    _exit(0);
		  }
#endif
#endif
		  qprint(n);
		  close(n);
		  MIBMtaEntry->sc.MQ1sockParallel --;
		  /* Silence memory debuggers about this child's
		     activities by doing exec() on the process.. */
		  /* execl("/bin/false","false",NULL); */
		  _exit(0); /* _exit() should be silent, too.. */
		}
		if (pid < 0)
		  MIBMtaEntry->sc.MQ1sockParallel --;
		close(n);
	      } else {
		/* mailqmode == 2 */

		MIBMtaEntry->sc.MQ2sockConnects ++;

#if 0  /* NOT IN MAILQ-V2 MODE ! */
#ifdef USE_TCPWRAPPER
#ifdef HAVE_TCPD_H /* TCP-Wrapper code */
		if (wantconn(n, "mailq") == 0) {
		  char *msg = "500 TCP-WRAPPER refusing 'mailq' query from your whereabouts\r\n";
		  int   len = strlen(msg);
		  write(n,msg,len);
		  MIBMtaEntry->sc.MQ2sockTcpWrapRej ++;
		  close(n);
		}
		else
#endif
#endif
#endif
		  mq2_register(n, &raddr);
	      }
	    }
	  }
	  if (query6fds) query6fds->revents = 0;

	  if (queryfds &&
	      (queryfds->revents & (ZM_POLLIN|ZM_POLLERR|ZM_POLLHUP))) {

	    Usockaddr raddr;
	    int raddrlen = sizeof(raddr);

	    n = accept(querysocket, (struct sockaddr *)&raddr, (void*)&raddrlen);
	    if (n >= 0) {
	      if (mailqmode == 1) {
		int pid;

		MIBMtaEntry->sc.MQ1sockConnects ++;
		MIBMtaEntry->sc.MQ1sockParallel ++;

		pid = fork();
		if (pid == 0) {
#if defined(F_SETFD)
		  fcntl(n, F_SETFD, 1); /* close-on-exec */
#endif
#ifdef USE_TCPWRAPPER
#ifdef HAVE_TCPD_H /* TCP-Wrapper code */
		  if (wantconn(n, "mailq") == 0) {
		    char *msg = "500 TCP-WRAPPER refusing 'mailq' query from your whereabouts\r\n";
		    int   len = strlen(msg);
		    write(n,msg,len);
		    MIBMtaEntry->sc.MQ1sockParallel --;
		    MIBMtaEntry->sc.MQ1sockTcpWrapRej ++;
		    _exit(0);
		  }
#endif
#endif
		  qprint(n);
		  close(n);
		  MIBMtaEntry->sc.MQ1sockParallel --;
		  /* Silence memory debuggers about this child's
		     activities by doing exec() on the process.. */
		  /* execl("/bin/false","false",NULL); */
		  _exit(0); /* _exit() should be silent, too.. */
		}
		if (pid < 0)
		  MIBMtaEntry->sc.MQ1sockParallel --;
		close(n);
	      } else {
		/* mailqmode == 2 */

		MIBMtaEntry->sc.MQ2sockConnects ++;

		mq2_register(n, &raddr);
	      }
	    }
	  }
	  if (queryfds) queryfds->revents = 0;

	}
}

void
queryipcinit()
{
	int modecode = 1; /* Modes: 1=TCP, 2=UNIX, default=TCP */
	char *modedata = NULL;

	while (notifysocket < 0) {

	  if (!notifysock) {
	    notifysock = (char *)getzenv("SCHEDULERNOTIFY");
	    if (notifysock) {
	      notifysock = zenvexpand(notifysock);
	    } else {
	      notifysock = strsave("UNIX:${POSTOFFICE}/.scheduler.notify");
	      notifysock = zenvexpand(notifysock);
	    }
	  }

	  if (notifysock) {
	    if (cistrncmp(notifysock,"UNIX:",5)==0) {
	      modedata = (char *)notifysock+5;
	      modecode = 2;
	    } else if (*notifysock == '/') {
	      /* If it begins with '/', it is AF_UNIX socket */
	      modedata = (char *)notifysock;
	      modecode = 2;
	    } else if (cistrncmp(notifysock,"UDP:",4)==0) {
	      modedata = (char *)notifysock+4;
	      modecode = 1;
	    } else {
	      /* The default mode is UDP/IP socket */
	      modedata = (char *)notifysock;
	      modecode = 1;
	    }
	  } else
	    modecode = 0;

	  /* Actually we support only AF_UNIX for the notify... */
#ifdef  AF_UNIX
	  if (modecode == 2) {
	    struct sockaddr_un sad;
	    int on = 1, oldumask;

	    memset(&sad, 0, sizeof(sad));
	    sad.sun_family = AF_UNIX;
	    strncpy(sad.sun_path, modedata, sizeof(sad.sun_path));
	    sad.sun_path[ sizeof(sad.sun_path)-1 ] = 0;

	    if ((notifysocket = socket(PF_UNIX, SOCK_DGRAM, 0)) < 0) {
	      perror("notifysocket: socket(PF_UNIX)");
	      break;
	    }

	    setsockopt(notifysocket, SOL_SOCKET, SO_REUSEADDR, (void*)&on, sizeof(on));

	    /* In case that one already exists.. */
	    unlink(sad.sun_path);

	    oldumask = umask(0577);

	    if (bind(notifysocket, (struct sockaddr *)&sad, sizeof sad) < 0) {
	      perror("bind:UNIX notify socket");
	      umask(oldumask);
	      close(notifysocket);
	      notifysocket = -1;
	      break;
	    }
	    umask(oldumask);

	    fcntl(notifysocket, F_SETFL,
		  fcntl(notifysocket, F_GETFL, 0)|O_NONBLOCK);

#if defined(F_SETFD)
	    fcntl(notifysocket, F_SETFD, 1); /* close-on-exec */
#endif
	  }
#endif /* AF_UNIX */
	  break;
	}

#if defined(AF_INET6) && defined(INET6)
	while (querysocket6 < 0) {

	  modedata = NULL;
	  modecode = 0;
	  if (mailqsock) {
	    if (cistrncmp(mailqsock,"UNIX:",5)==0) {
	      modedata = (char *)mailqsock+5;
	      modecode = 2;
	    } else if (*mailqsock == '/') {
	      /* If it begins with '/', it is AF_UNIX socket */
	      modedata = (char *)mailqsock;
	      modecode = 2;
	    } else if (cistrncmp(mailqsock,"TCP:",4)==0) {
	      modedata = (char *)mailqsock+4;
	      modecode = 1;
	    } else {
	      /* The default mode is TCP/IP socket */
	      modedata = (char *)mailqsock;
	      modecode = 1;
	    }
	  } else {
	    /* The default mode is TCP/IP socket */
	    modedata = (char *)mailqsock;
	    modecode = 1;
	  }

	  if (modecode == 1) {
	    struct servent *serv;
	    Usockaddr ua;
	    int on = 1;
	    int port = 174;
	    char *modedata2 = NULL;

	    if (modedata) {
	      modedata2 = strchr(modedata,'@');
	      if (modedata2) *modedata2++ = 0;
	    }

	    if (!modedata || !*modedata || sscanf(modedata,"%d",&port) != 1) {
	      serv = getservbyname(modedata ? modedata : "mailq", "tcp");
	      if (serv == NULL) {
		sfprintf(sfstderr, "No 'mailq' tcp service defined!\n");
		port = 174; /* magic knowledge */
	      } else
		port = ntohs(serv->s_port);
	    }
	    if (modedata2)  modedata2[-1] = '@';

	    querysocket6 = socket(PF_INET6, SOCK_STREAM, 0);
	    if (querysocket6 < 0) {
	      perror("querysocket6: socket(PF_INET6) fail");
	      break;
	    }

	    memset( & ua, 0, sizeof(ua) );
#if 0
	    zgetbindaddr(NULL, AF_INET6, &ua); /* error returns
						  without setting
						  anything. */
#endif
	    ua.v6.sin6_family   = AF_INET6;
	    ua.v6.sin6_flowinfo = 0;
	    ua.v6.sin6_port     = htons(port);

	    setsockopt(querysocket6, SOL_SOCKET, SO_REUSEADDR, (void*)&on, sizeof(on));
#ifdef SO_REUSEPORT
	    setsockopt(querysocket6, SOL_SOCKET, SO_REUSEPORT, (void*)&on, sizeof(on));
#endif

	    if (bind(querysocket6,(struct sockaddr*)&ua,sizeof(ua.v6)) < 0) {
	      perror("bind:TCP6 mailq socket");
	      close(querysocket6);
	      querysocket6 = -1;
	      break;
	    }

	    fd_nonblockingmode(querysocket6);

#if defined(F_SETFD)
	    fcntl(querysocket6, F_SETFD, 1); /* close-on-exec */
#endif
	    if (listen(querysocket6, 5) < 0) {
	      perror("listen:TCP6 mailq socket");
	      close(querysocket6);
	      querysocket6 = -1;
	      break;
	    }
	  }
	  break;
	}
#endif /* defined(AF_INET6) && defined(INET6) */

	while (querysocket < 0) {

	  modedata = NULL;
	  modecode = 0;
	  if (mailqsock) {
	    if (cistrncmp(mailqsock,"UNIX:",5)==0) {
	      modedata = (char *)mailqsock+5;
	      modecode = 2;
	    } else if (*mailqsock == '/') {
	      /* If it begins with '/', it is AF_UNIX socket */
	      modedata = (char *)mailqsock;
	      modecode = 2;
	    } else if (cistrncmp(mailqsock,"TCP:",4)==0) {
	      modedata = (char *)mailqsock+4;
	      modecode = 1;
	    } else {
	      /* The default mode is TCP/IP socket */
	      modedata = (char *)mailqsock;
	      modecode = 1;
	    }
	  } else {
	    /* The default mode is TCP/IP socket */
	    modedata = (char *)mailqsock;
	    modecode = 1;
	  }

#ifdef  AF_UNIX
	  if (modecode == 2) {
	    struct sockaddr_un sad;
	    int on = 1, oldumask;

	    memset(&sad, 0, sizeof(sad));
	    sad.sun_family = AF_UNIX;
	    strncpy(sad.sun_path, modedata, sizeof(sad.sun_path));
	    sad.sun_path[ sizeof(sad.sun_path)-1 ] = 0;

	    if ((querysocket = socket(PF_UNIX, SOCK_STREAM, 0)) < 0) {
	      perror("querysocket: socket(PF_UNIX)");
	      break;
	    }

	    setsockopt(querysocket, SOL_SOCKET, SO_REUSEADDR, (void*)&on, sizeof(on));

	    /* In case that one already exists.. */
	    unlink(sad.sun_path);

	    oldumask = umask(0111);

	    if (bind(querysocket, (struct sockaddr *)&sad, sizeof sad) < 0) {
	      perror("bind:UNIX mailq socket");
	      umask(oldumask);
	      close(querysocket);
	      querysocket = -1;
	      break;
	    }
	    umask(oldumask);

	    fd_nonblockingmode(querysocket);

#if defined(F_SETFD)
	    fcntl(querysocket, F_SETFD, 1); /* close-on-exec */
#endif

	    if (listen(querysocket, 5) < 0) {
	      perror("listen:UNIX mailq socket");
	      close(querysocket);
	      querysocket = -1;
	      break;
	    }
	  }
#endif /* AF_UNIX */
#ifdef AF_INET
	  if (modecode == 1) {
	    struct servent *serv;
	    Usockaddr ua;
	    int on = 1;
	    int port = 174;
	    char *modedata2 = NULL;

	    if (modedata) {
	      modedata2 = strchr(modedata,'@');
	      if (modedata2) *modedata2++ = 0;
	    }

	    if (!modedata || !*modedata || sscanf(modedata,"%d",&port) != 1) {
	      serv = getservbyname(modedata ? modedata : "mailq", "tcp");
	      if (serv == NULL) {
		sfprintf(sfstderr, "No 'mailq' tcp service defined!\n");
		port = 174; /* magic knowledge */
	      } else
		port = ntohs(serv->s_port);
	    }
	    if (modedata2)  modedata2[-1] = '@';

	    memset(&ua, 0, sizeof(ua));
	    if (zgetbindaddr(NULL, AF_INET, &ua))
		ua.v4.sin_addr.s_addr = htonl(INADDR_ANY);
	    ua.v4.sin_port        = htons(port);
	    ua.v4.sin_family      = AF_INET;
	    querysocket = socket(PF_INET, SOCK_STREAM, 0);
	    if (querysocket < 0) {
	      perror("querysocket: socket(PF_INET)");
	      break;
	    }
	    setsockopt(querysocket, SOL_SOCKET, SO_REUSEADDR, (void*)&on, sizeof(on));
	    if (bind(querysocket, (struct sockaddr *)&ua, sizeof ua.v4) < 0) {
	      perror("bind:TCP4 mailq socket");
	      close(querysocket);
	      querysocket = -1;
	      break;
	    }

	    fcntl(querysocket, F_SETFL,
		  fcntl(querysocket, F_GETFL, 0)|O_NONBLOCK);


#if defined(F_SETFD)
	    fcntl(querysocket, F_SETFD, 1); /* close-on-exec */
#endif

	    if (listen(querysocket, 5) < 0) {
	      perror("listen:TCP mailq socket");
	      close(querysocket);
	      querysocket = -1;
	      break;
	    }
	  }
#endif	/* AF_INET */
	  break;
	}

	if ((querysocket >= 0 || querysocket6 >= 0) && notifysocket >= 0) {
	  qipcretry = 0; /* Successfull init done. */
	  
	} else {
	  mytime(&now); 
	  qipcretry = now + 5; /* Will do retry soon.. */
	}
}


static void readfrom(fd)
	int fd;
{
	int	n, e, bufsize = 2048;
	char	*cp, *eobuf, *buf;
	struct procinfo *proc = &cpids[fd];

	cp = buf = (char *)emalloc(bufsize);

	if (proc->carryover != NULL) {
	  int carrylen = strlen(proc->carryover);
	  if (carrylen > bufsize) {
	    while (carrylen > bufsize)
	      bufsize += 1024;
	    buf = erealloc(buf,bufsize);
	  }
	  strcpy(buf, proc->carryover);
	  cp = buf+strlen(buf);
	  free(proc->carryover);
	  proc->carryover = NULL;
	}

	/* Note that if we get an alarm() call, the read will return -1, TG */
	errno = 0;
	while ((n = read(fd, cp, bufsize - (cp - buf))) > 0) {

	  if (verbose)
	    sfprintf(sfstderr, "read from %d returns %d\n", fd, n);

	  eobuf = cp + n;

	  for (cp = buf; cp < eobuf;) {
	    if (*cp == '\n') {
	      int rlen = eobuf - (cp+1);
	      *cp = '\0';
	      if (verbose)
		sfprintf(sfstderr, "%p %d fd=%d processed: %s\n",
			 proc, (int)proc->pid, fd, buf);
	      update(fd,buf);
	      ++cp;
	      if (rlen > 0)
		memcpy(buf, cp, rlen);
	      else
		rlen = 0;
	      cp = buf;
	      eobuf = buf + rlen;

	    } else

	      ++cp;
	  }

	  if (cp == (buf + bufsize)) {
	    /* 
	     * can't happen, this would mean a status report line 
	     * that is rather long...
	     * (oh no! it did happen, it did, it did!...)
	     */
	    int oldsize = bufsize;
	    bufsize <<= 1;
	    buf = erealloc(buf,bufsize);
	    cp = buf + oldsize;
	    *cp = '\0';
	  }

	}
	e = errno;

	if (verbose) {
	  if (!(e == EAGAIN || e == EWOULDBLOCK))
	    sfprintf(sfstderr,
		    "read from %d returns %d, errno=%d\n", fd, n, e);
	}
	if (n == 0 || (n < 0 && !(e == EWOULDBLOCK ||
				  e == EAGAIN || e == EINTR))) {
	  /*sfprintf(sfstdout,
	    "about to call waitandclose(), n=%d, errno=%d\n",n,e);*/

	  if (proc->tofd >= 0)
	    pipes_shutdown_child(proc->tofd);
	  proc->tofd = -1;
	  waitandclose(fd);
	}

	/* sfprintf(sfstderr, "n = %d, errno = %d\n", n, errno); */
	/*
	 * if n < 0, then either we got an interrupt or the read would
	 * block (EINTR or EWOULDBLOCK). In both cases we basically just
	 * want to get back to whatever we were doing. We just need to
	 * make darned sure that a newline was the last character we saw,
	 * or else some report may get lost somewhere.
	 */
	if (proc->pid != 0) {
	  proc->carryover = emalloc(cp - buf + 1);
	  memcpy(proc->carryover, buf, cp - buf);
	  proc->carryover[cp - buf] = '\0';
	} else if (cp > buf)
	  sfprintf(sfstderr,
		   "HELP! Lost %ld bytes (n=%d/%d): '%s'\n",
		   (long)(cp - buf), n, errno, buf);
	free(buf);
}

#if 0 /* System does not use MKDIR/RMDIR anymore.. */
#if defined(USE_BINMKDIR) || defined(USE_BINRMDIR)

/*
 * From Ross Ridge's Xenix port:
 * - A nasty problem occurs with scheduler if rmdir (and mkdir also I think),
 *   is implented as system("/bin/rmdir ...").  When system() calls wait()
 *   it can reap the scheduler's children without it knowing.  I fixed this
 *   problem by writing a replacement system() function for scheduler.
 *
 */

int
system(name)
	char *name;
{
	char *sh;
	int st, r;
	int pid;
	int i;

	pid = fork();
	switch(pid) {
	case -1:
		return -1;
	case 0:
		sh = getenv("SHELL");
		if (sh == NULL) {
		  sh = "/bin/sh";
		}
		execl(sh, sh, "-c", name, NULL);
		_exit(1);
	default:
#ifndef USE_SIGREAPER
		while(1) {
		  r = wait(&st);
		  if (r == -1) {
		    if (errno != EINTR) {
		      return -1;
		      if (errno != EINTR) {
			return -1;
		      }
		    } else if (r == pid) {
		      break;
		    }
		    for(i = 0; i < scheduler_nofiles; i++) {
		      if (cpids[i].pid == r) {
			cpids[i].pid = -r;
			break;
		      }
		    }
		  }

		  if ((st & 0x00ff) == 0) {
		    return st >> 8;
		  }
		  return 1;
		}
#endif
		break;
	   }
}

#endif
#endif


#ifdef USE_SIGREAPER
/*
 *	Catch each child-process death, and reap them..
 */
RETSIGTYPE sig_chld(signum)
int signum;
{
	int pid;
	int ok = 0;
	int i;
	int statloc;

	for (;;) {

#ifdef	HAVE_WAITPID
	  pid = waitpid(-1, &statloc, WNOHANG);
#else
#ifdef  HAVE_WAIT4
	  pid = wait4(0, &statloc, WNOHANG, NULL);
#else
#ifdef  HAVE_WAIT3
	  pid = wait3(&statloc, WNOHANG, NULL);
#else
	  pid = wait(&statloc);
#endif
#endif
#endif
	  if (pid <= 0) break;

	  if (WIFEXITED  (statloc)) ok = 1;
	  if (WIFSIGNALED(statloc)) ok = 1;

	  if (verbose) {
	    sfprintf(sfstderr,"sig_chld() pid=%d, ok=%d, stat=0x%x ",
		    pid,ok,statloc);
	    if (WIFEXITED  (statloc))
	      sfprintf(sfstderr,"EXIT=%d\n", WEXITSTATUS(statloc));
	    if (WIFSIGNALED(statloc))
	      sfprintf(sfstderr,"SIGNAL=%d\n", WTERMSIG(statloc));
	  }

	  if (ok && cpids != NULL) {
	    /* Only EXIT and SIGxx DEATHS accepted */

	    for (i = scheduler_nofiles-1; i >= 0; --i) {
	      if (cpids[i].pid == pid) {
		cpids[i].pid = -pid; /* Mark it as reaped.. */
		cpids[i].reaped = 1;
		cpids[i].waitstat = statloc;
		ok = 0;
		if (WSIGNALSTATUS(statloc) == 0 &&
		    WEXITSTATUS(statloc)   == EX_SOFTWARE) {
		  zsyslog((LOG_EMERG, "Transporter process %d exited with EX_SOFTWARE!", pid));
		  sfprintf(sfstderr, "Transporter process %d exited with EX_SOFTWARE; cmdline='%s'\n", pid, cpids[i].cmdline);
		}
		break;
	      }
	      if (cpids[i].pid == -pid) {
		sfprintf(sfstdout," .. already reaped ??\n");
		cpids[i].pid = -pid; /* Mark it as reaped.. */
		cpids[i].reaped = 1;
		cpids[i].waitstat = statloc;
		ok = 0;
		break;
	      }
	    }
	  }
	}

	/* re-instantiate the signal handler.. */
#ifdef SIGCLD
	SIGNAL_HANDLE(SIGCLD,  sig_chld);
#else
	SIGNAL_HANDLE(SIGCHLD, sig_chld);
#endif
}
#endif /* USE_SIGREAPER */
