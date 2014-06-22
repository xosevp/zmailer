/*
 *	Copyright 1990 by Rayan S. Zachariassen, all rights reserved.
 *	This will be free software, but only when it is finished.
 */
/*
 *	Lots of modifications (new guts, more or less..) by
 *	Matti Aarnio <mea@nic.funet.fi>  (copyright) 1992-2007
 */

#include "hostenv.h"
#include <sfio.h>
#include "scheduler.h"
#include "prototypes.h"

int	/* return non-zero when there are some childs
	   available for start				*/
doagenda()
{
	struct thread *thr, *nthr;
	int didsomething = 0;

	timed_log_reinit(); /* 	internal: mytime(&now); */


	thr = thread_head;

	if (verbose)
	  sfprintf(sfstdout,"curitem %p curitem->wakeup %lu now %d\n",
		   thr, thr ? thr->wakeup : 0, (int)now);

	/* thread_head -chain should be in time order, thus
	   the while-loop should be traversed only once, because
	   thread_start kicks  right away (or reschedules) */

	for ( ; thr  && thr->wakeup <= now ; thr = nthr ) {
	  /* Object pointed by  thr  may disappear due to
	     expiration at thread_start() .. */
	  nthr = thr->nexttr;

	  /* Not running, and wakeup in past ? */

	  if (thr->proc == NULL && thr->wakeup <= now) {
	    /* Try to start it! */

	    while (thread_start(thr, 0))
	      ++ didsomething;

	  }

	  queryipccheck(); /* updates the 'now' variable too... */
	}

	/* if (verbose)
	   printf("alarmed %d\n", now);  */

	return (didsomething);
}


int	/* Return the number of messages expired this time around. */
doexpiry2()
{
	struct thread *thr, *nthr;
	int didsomething = 0, rc;
	time_t timelimit;

	timed_log_reinit(); /* 	internal: mytime(&now); */

	timelimit = now + expiry2_timelimit;

	thr = thread_head;

	if (verbose)
	  sfprintf(sfstdout,"curitem %p curitem->wakeup %lu now %d\n",
		   thr, thr ? thr->wakeup : 0, (int)now);

	/* thread_head -chain should be in time order, thus
	   the while-loop should be traversed only once, because
	   thread_start kicks right away (or reschedules) */

	for ( ; thr  && thr->wakeup <= now ; thr = nthr ) {
	  /* Object pointed by  thr  may disappear due to
	     expiration at thread_start() .. */
	  nthr = thr->nexttr;

	  rc = thread_expire2(thr, timelimit, 0, NULL);
	  if (rc)
	    didsomething += rc;

	  queryipccheck(); /* updates the 'now' variable too... */

	  if (now > timelimit) break;
	}

	/* if (verbose)
	   printf("alarmed %d\n", now);  */

	return (didsomething);
}


/* Do immediate scheduling of given host-indentifier. */
int
turnme(turnarg)
const char *turnarg;
{
	struct spblk *spl;
	struct web *wp;
	char *cp = strchr(turnarg,' ');
	struct thread *thr, *nthr;
	spkey_t spk;
	int rc = 0;

	/* caller has done 'strlower()' to our input.. */
	if (cp) *cp = 0;  /* Chop at the first SPACE or TAB */
	cp = strchr(turnarg,'\t');
	if (cp) *cp = 0;

	spk = symbol_lookup_db((void*)turnarg, spt_mesh[L_HOST]->symbols);
	spl = sp_lookup(spk, spt_mesh[L_HOST]);
	if (spl == NULL || spl->data == NULL) {
	  /* Not found, nothing to do.. */
	  return 0;
	}
	wp = (struct web *)spl->data;
	
	thr = thread_head;
	while (thr != NULL) {
	  /* Object pointed by  thr  may disappear due to
	     expiration at thread_start()	 */
	  nthr = thr->nexttr;

	  if (wp == thr->whost && thr->proc == NULL) {
	    thr->wakeup = 0; /* Force its starttime! */
	    rc += thread_start(thr, 1);
	    /* We MAY get multiple matches, though it is unlikely.. */
	  }
	  thr = nthr;
	}
	return rc;
}   
