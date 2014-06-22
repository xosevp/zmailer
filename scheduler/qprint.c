/*
 *	Copyright 1988 by Rayan S. Zachariassen, all rights reserved.
 *	This will be free software, but only when it is finished.
 */
/*
 *	Lots of modifications (new guts, more or less..) by
 *	Matti Aarnio <mea@nic.funet.fi>  (copyright) 1992-1999-2003-2007
 */

#include "hostenv.h"
#include <sfio.h>
#include "scheduler.h"
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>

#include "prototypes.h"
#include "libz.h"

/* define NO_VERBOSE_MAILQ, if you don't want to output potentially HUGE
   mailq report -- necessary at some sites, while definitely undesirable
   at others..  We need to change this mechanism.. */
extern int mailq_Q_mode; /* Argument 'Q' means: output only 'mailq -Q' -data.. */
/* #define NO_VERBOSE_MAILQ */

extern int errno;

static int qpctlfile __((void *, struct spblk *spl));
static int qpchannel __((void *, struct spblk *spl));
static int qphost __((void *, struct spblk *spl));

#ifdef HAVE_SYS_TIME_H
# include <sys/time.h>
#endif	/* !HAVE_UTIMES */
#ifdef HAVE_UTIME_H
# include <utime.h>
#else
/* XXX: struct utimbuf defined ??? */
#endif

static char qpch;
static time_t qpnow;

static int qid = 0;

void
qprint(fd)
	int fd;
{
#ifdef	HAVE_UTIME
	struct utimbuf tvp;
#else	/* !HAVE_UTIMES */
	struct timeval tvp[2];
#endif	/* !HAVE_UTIMES */
	Sfio_t *qpfp;

	/*
	 * The O_NDELAY flag is needed so we don't block
	 * if the file is a FIFO (which is recommended).
	 */
	if (fd < 0) {
#ifndef O_NDELAY
#define O_NDELAY 0	/* you lose */
#endif
	  fd = open(rendezvous, O_WRONLY|O_CREAT|O_TRUNC|O_NDELAY, 0644);
	  if (fd < 0) {
	    sfprintf(sfstderr,"open(%s): %d\n", rendezvous, errno);
	    return;
	  }
	}
	if ((qpfp = sfnew(NULL, NULL, 0, fd, SF_WRITE)) == NULL) {
	  sfprintf(sfstderr, "hmmm\n");
	  close(fd);
	  return;
	}
	qpch = '\0';
	qid  = 0;

	sfprintf(qpfp, "version zmailer 1.0\nVertices:\n");
	mytime(&qpnow);
#ifndef NO_VERBOSE_MAILQ
	if (!mailq_Q_mode)
	  sp_scan(qpctlfile, qpfp, (struct spblk *)NULL, spt_mesh[L_CTLFILE]); 
#endif
	if (qpch != '\0') {
	  sfprintf(qpfp, "Channels:\n");
#ifndef NO_VERBOSE_MAILQ
	  if (!mailq_Q_mode)
	    sp_scan(qpchannel, qpfp, (struct spblk *)NULL, spt_mesh[L_CHANNEL]);
#endif
	  sfprintf(qpfp, "Hosts:\n");
#ifndef NO_VERBOSE_MAILQ
	  if (!mailq_Q_mode)
	    sp_scan(qphost, qpfp, (struct spblk *)NULL, spt_mesh[L_HOST]);
#endif
	}
	sfprintf(qpfp, "End:\n");

	thread_report(qpfp, MQ2MODE_FULL);
	
	sfclose(qpfp);

	/* XX: I suppose we don't really need to do this if we use TCP. */
	if (rendezvous != NULL) {
	  now = mytime(NULL) - 1;
#ifdef	HAVE_UTIME
	  tvp.actime = tvp.modtime = now;
	  utime(rendezvous, &tvp);
#else	/* !HAVE_UTIMES */
	  tvp[0].tv_sec = tvp[1].tv_sec = now;
	  tvp[0].tv_usec = tvp[1].tv_usec = 0;
	  utimes(rendezvous, tvp);
#endif	/* !HAVE_UTIMES */
	}
}

static int qpctlfile(p, spl)
	void *p;
	struct spblk *spl;
{
	register struct ctlfile *cfp = (struct ctlfile *)spl->data;
	register struct vertex *vp;
	register int i;
	char buf[100];
	Sfio_t *qpfp = p;

	/* assert cfp != NULL */
	for (vp = cfp->head; vp != NULL; vp = vp->next[L_CTLFILE]) {
	  vp->qid = ++qid;
	  sfprintf(qpfp, "%d:\t%s%s\t%d;",
		   vp->qid, cfpdirname(cfp->dirind), cfp->mid, vp->ngroup);
	  qpch = ' ';
	  for (i = 0; i < vp->ngroup; ++i) {
	    sfprintf(qpfp, "%c%ld", qpch, (long)cfp->offset[vp->index[i]]);
	    qpch = ',';
	  }
	  if (vp->message != NULL)
	    sfprintf(qpfp, "\t#%s ", vp->message);
	  else
	    sfprintf(qpfp, "\t#");

	  i = 0;
	  if (vp->thread->wakeup > qpnow) {
	    buf[0] = '\0';
	    saytime((u_long)(vp->thread->wakeup - qpnow), buf, 1);
	    sfprintf(qpfp, "(retry in %s", buf);
	    ++i;
	  } else if (vp->ce_pending) {
	    sfprintf(qpfp, "(waiting for %sslot",
		     vp->ce_pending == SIZE_L ? "" :
		     vp->ce_pending == L_CHANNEL ? "channel " :
		     "thread ");
	    ++i;
	  } else {
	    if (vp->thread && vp->thread->proc) {
	      sfprintf(qpfp,"(running now, pid=%d",
		       (int)vp->thread->proc->pid);
	      /* MULTI-TA-PER-THREAD ?? */
	      if (vp->thread->nextfeed == vp)
		sfprintf(qpfp," NextFeed");
	    } else {
	      sfprintf(qpfp, "(activation pending, thread");
	      /* A vertex is always on some thread.. */
	      if (vp->thread && vp->thread->proc) {
		sfprintf(qpfp," pid=%d ", (int)vp->thread->proc->pid);
	      } else {
		if (vp->thread == NULL)
		  sfprintf(qpfp," NO_THREAD!");
		else
		  sfprintf(qpfp," inactive");
	      }
	    }
	    ++i;
	  }
	  if (vp->ce_expiry > 0) {
	    /* [mea] Want to know when it expires.. */
	    buf[0] = '\0';
	    saytime((long)(vp->ce_expiry - qpnow), buf, 1);
	    sfprintf(qpfp,"%sexpires in %s, tries=%d",
		     i ? ", " : "(", buf, vp->attempts);
	  }
	  if (i)
	    sfputc(qpfp, ')');

	  sfputc(qpfp, '\n');
	}
	  return 0;
	}

static int qpchannel(p, spl)
	void *p;
	struct spblk *spl;
{
	register struct web *wc = (struct web *)spl->data;
	register struct vertex *vp;
	register Sfio_t *qpfp = p;

	if (wc->link != NULL) {
	  sfprintf(qpfp, "%s:\t", wc->name);
	  for (vp = wc->link; vp != NULL; vp = vp->next[L_CHANNEL])
	    if (vp->qid)
	      sfprintf(qpfp, ">%d", vp->qid);
	    else
	      sfprintf(qpfp, ">999%04d", (int)vp->cfp->id);
	  sfprintf(qpfp, "\n");
	}
	return 0;
}

static int qphost(p, spl)
	void *p;
	struct spblk *spl;
{
	register struct web *wc = (struct web *)spl->data;
	register struct vertex *vp;
	register Sfio_t *qpfp = p;

	if (wc->link != NULL) {
	  sfprintf(qpfp, "%s:\t", wc->name);
	  for (vp = wc->link; vp != NULL; vp = vp->next[L_HOST])
	    if (vp->qid)
	      sfprintf(qpfp, ">%d", vp->qid);
	    else
	      sfprintf(qpfp, ">999%04d", (int)vp->cfp->id);
	  sfprintf(qpfp, "\n");
	}
	return 0;
}
