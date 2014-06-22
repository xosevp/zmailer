/*
 *	ZMailer 2.99.16+ Scheduler "threads" routines
 *
 *	Copyright Matti Aarnio <mea@nic.funet.fi> 1995-2007
 *
 *	These "threads" are for book-keeping of information
 *	regarding schedulable recipient vertices
 */

#include <stdio.h>
#include <sfio.h>
#include <ctype.h>
#include <unistd.h>
#include "scheduler.h"
#include "prototypes.h"
#include "zsyslog.h"
#include "libz.h"
/* #include <stdlib.h> */

/*
   Each vertex arrives into SOME thread, each of which belong to
   SOME thread-group, among which groups the transport channel
   programs started for any member thread can be shared among
   their members.
*/


#define MAX_HUNGER_AGE 600 /* Sign of an error ... */

extern char *proc_state_names[];

struct thread      *thread_head = NULL;
struct thread      *thread_tail = NULL;

static struct threadgroup *thrg_root   = NULL;
int idleprocs = 0;
extern int global_wrkcnt;
extern int syncstart;
extern int freeze;
extern int slow_shutdown;
extern time_t now;
extern char *procselect, *procselhost;
extern time_t sched_starttime; /* From main() */
extern int mailqmode;	/* 1 or 2 */

static long groupid  = 0;
static long threadid = 0;

static void  thread_vertex_shuffle __((struct thread *thr));
static struct threadgroup *create_threadgroup __((struct config_entry *cep, struct web *wc, struct web *wh, int withhost, void (*ce_fillin)__((struct threadgroup *, struct config_entry *)) ));
static int   thread_start_ __((struct thread *thr));


static struct threadgroup *
create_threadgroup(cep, wc, wh, withhost, ce_fillin)
struct config_entry *cep;
struct web *wc, *wh;
int withhost;
void (*ce_fillin) __((struct threadgroup*, struct config_entry *));
{
	struct threadgroup *thgp;

	/* Create a thread-group and link it into group-ring */

	thgp = (struct threadgroup*)malloc(sizeof(*thgp));
	if (!thgp) return NULL;
	memset(thgp,0,sizeof(*thgp));

	++groupid;
	thgp->groupid  = groupid;

	thgp->cep      = cep;
	thgp->withhost = withhost;
	thgp->wchan    = wc;
	thgp->whost    = wh;

	ce_fillin(thgp,cep);

	wc->linkcnt += 1;
	wh->linkcnt += 1;

	if (thrg_root == NULL) {
	  thrg_root     = thgp;
	  thgp->nextthg = thgp;
	  thgp->prevthg = thgp;
	} else {
	  thgp->nextthg       = thrg_root->nextthg;
	  thgp->prevthg       = thrg_root->nextthg->prevthg;
	  thgp->prevthg->nextthg = thgp;
	  thgp->nextthg->prevthg = thgp;
	}

	return thgp;
}

void
delete_threadgroup(thgp)
struct threadgroup *thgp;
{
	struct threadgroup *tgp;

	/* Time to say good-bye to this group, delete it.
	   We shall not have any threads under us, nor
	   idle processes!				  */

	/* However we may be called with either of these values
	   still non-zero... */
	if (thgp->transporters || thgp->threads) return;

if (verbose) sfprintf(sfstderr,"delete_threadgroup(%s/%d/%s)\n",
		      thgp->wchan->name,thgp->withhost,thgp->whost->name);

	if (thgp->idleproc != NULL || thgp->thread != NULL)
	  abort(); /* Deleting non-empty thread-group! */
	if (thrg_root == NULL) abort(); /* No thread-group root! */


	/* We are possibly the last to keep these web links */

	thgp->wchan->linkcnt -= 1;
	unweb(L_CHANNEL,thgp->wchan);

	thgp->whost->linkcnt -= 1;
	unweb(L_HOST,thgp->whost);

	/* Unlink this thread-group from the ring */

	tgp                    = thgp->nextthg;
	thgp->prevthg->nextthg = thgp->nextthg;
	tgp->prevthg           = thgp->prevthg;

	/* are we at the ring root pointer ? */
	if (thrg_root == thgp)
	  thrg_root = tgp;
	if (tgp == thgp) {
	  /* We were the only one! */
	  thrg_root = NULL;
	}

memset(thgp, 0x55, sizeof(*thgp));

	free(thgp);
}

static void _thread_timechain_unlink __((struct thread *));
static void _thread_timechain_unlink(thr)
struct thread *thr;
{
	struct threadgroup *thg = thr->thgrp;

	/* Doubly linked linear list */

	if (thr->prevtr != NULL)
	  thr->prevtr->nexttr = thr->nexttr;
	if (thr->nexttr != NULL)
	  thr->nexttr->prevtr = thr->prevtr;

	if (thread_head == thr)
	  thread_head = thr->nexttr;
	if (thread_tail == thr)
	  thread_tail = thr->prevtr;

	thr->nexttr = NULL;
	thr->prevtr = NULL;

	/* Doubly linked circullar list */

	thr->prevthg->nextthg = thr->nextthg;
	thr->nextthg->prevthg = thr->prevthg;

	thg->threads                      -= 1;
	MIBMtaEntry->sc.StoredThreadsSc -= 1;

	if (thg->thread == thr)
	  thg->thread = thr->nextthg;	/* pick other */
	if (thg->thread == thr)
	  thg->thread = NULL;		/* was the only one! */

	if (thg->thrtail == thr)
	  thg->thrtail = thr->prevthg;	/* pick other */
	if (thg->thrtail == thr)
	  thg->thrtail = NULL;		/* was the only one! */

	thr->prevthg = NULL;
	thr->nextthg = NULL;
}

static void _thread_timechain_append __((struct thread *));
static void _thread_timechain_append(thr)
struct thread *thr;
{
	struct threadgroup *thg = thr->thgrp;

	/* Doubly linked linear list */

	if (thread_head == NULL) {

	  thread_head = thr;
	  thread_tail = thr;
	  thr->nexttr = NULL;
	  thr->prevtr = NULL;

	} else {

	  thread_tail->nexttr = thr;
	  thr->nexttr = NULL;
	  thr->prevtr = thread_tail;
	  thread_tail = thr;

	}

	/* Doubly linked circullar list */

	if (thg->thread == NULL) {

	  thg->thread  = thr;
	  thg->thrtail = thr;
	  thr->nextthg = thr;
	  thr->prevthg = thr;

	} else {

	  thr->nextthg = thg->thrtail->nextthg;
	  thg->thrtail->nextthg = thr;
	  thr->prevthg = thr->nextthg->prevthg;
	  thr->nextthg->prevthg = thr;

	  thg->thrtail = thr;

	}

	thg->threads += 1;
	MIBMtaEntry->sc.StoredThreadsSc += 1;
}


static struct thread *create_thread __((struct threadgroup *thgrp,
					struct vertex *vtx,
					struct config_entry *cep));

static struct thread *
create_thread(thgrp, vtx, cep)
struct threadgroup *thgrp;
struct vertex *vtx;
struct config_entry *cep;
{
	/* Create a thread-block, link in the group pointer,
	   and link the thread into thread-ring, plus APPEND
	   to the thread time-chain				*/

	struct thread *thr;
	thr = (struct thread *)emalloc(sizeof(*thr));
	if (!thr) return NULL;

	memset(thr,0,sizeof(*thr));

	++threadid;
	thr->threadid = threadid;

	/* thr->attempts = 0;
	   thr->nextthg = NULL;
	   thr->prevthg = NULL; */

	thr->thgrp   = thgrp;
	thr->wchan   = vtx->orig[L_CHANNEL];
	thr->whost   = vtx->orig[L_HOST];

	if (thgrp->cep->flags & CFG_QUEUEONLY) {
		/* Start with the first retry */
		if(thgrp->cep->nretries) {
			mytime(&now);
			thr->wakeup = now + thgrp->cep->retries[0];
		}
	}

	thr->thvertices   = vtx;
	thr->lastthvertex = vtx;
	thr->jobs       = 1;

	vtx->thread     = thr;
	thr->channel    = strsave(vtx->orig[L_CHANNEL]->name);
	thr->host       = strsave(vtx->orig[L_HOST   ]->name);

	if (verbose) sfprintf(sfstderr,"create_thread(%s/%d/%s) -> %p\n",
			      thr->channel,thgrp->withhost,thr->host,thr);

	_thread_timechain_append(thr);

	return thr;
}


/*
 * Pick next thread from the group which this process serves.
 * At call the proc->pthread->proc does not contain us!
 *
 * Result is  proc->pthread  and  proc->pthread->nextfeed  being
 * updated to new thread, and function returns 1.
 * If no new thread can be picked (all are active, and whatnot),
 * return 0.
 */

int
pick_next_thread(proc)
     struct procinfo *proc;
{
	struct thread	    *thr;
	struct thread       *thr0 = proc->pthread;
	struct threadgroup  *thg  = proc->thg;
	int once;

	proc->pthread = NULL;

	if (thg->cep->flags & CFG_QUEUEONLY)
	  return 0; /* We are QUEUE ONLY group, no auto-switch! */

	mytime(&now);

	for ( thr = thg->thread, once = 1;
	      thr && (once || (thr != thg->thread));
	      thr = thr->nextthg, once = 0 ) {

	  struct vertex  * vp = thr->thvertices;
	  struct config_entry *ce = &(thr->thgrp->ce);

	  if (thr == thr0)
	    continue; /* No, can't be what we just were! */

	  if ((thr->wakeup > now) && (thr->attempts > 0))
	    continue; /* wakeup in future, unless first time around! */

	  if (vp && (thr->thrkids < ce->maxkidThread) &&
	      (thr->thrkids < thr->jobs) /* FIXME: real unfed count ? */) {

	    struct web     * ho = vp->orig[L_HOST];
	    struct web     * ch = vp->orig[L_CHANNEL];

	    if (thr->proc && thr->nextfeed == NULL)
	      continue; /* Nothing more to feed! See other threads! */

	    if (proc->ch != ch) /* MUST have same CH data - in case we ever
				   run with a clause where channel side is
				   partially wild-carded.. */
	      continue;

	    proc->pthread = thr;
	    thr->thrkids += 1;

	    if (thr->proc == NULL) {
	      /* Randomize the  order of thread vertices
		 (or sort by spool file mtime, if in AGEORDER..) */
	      /* Also init thr->nextfeed */
	      thread_vertex_shuffle(thr);
	    }

	    if (thr->proc)
	      proc->pnext = thr->proc;
	    thr->proc     = proc;
	    if (proc->pnext)
	      proc->pnext->pprev = proc;

	    if (proc->ho != NULL && proc->ho != ho) {
	      /* Get rid of the old host web */
	      proc->ho->kids -= 1;
	      unweb(L_HOST,proc->ho);
	      proc->ho = NULL;
	    }

	    /* Move the kid to this host web */
	    
	    if (proc->ho != ho) {
	      proc->ho = ho;
	      proc->ho->kids += 1;
	    }

	    /* The channel is be the same at old and new threads */

	    /* Move the pickup pointer forward.. */
	    thg->thread = thg->thread->nextthg;

	    if (thr->nextfeed == NULL) {
	      thr->pending = "NoNextFeed";
	      return 0;
	    }

	    return 1;
	  }
	}
	/* No result :-( */
	return 0;
}


int
delete_thread(thr)
     struct thread *thr;
{
	/* Unlink this thread from thread-chain, and thread
	   group.  Decrement thread-group count		    */

	struct threadgroup *thg = thr->thgrp;

	if (thr->thrkids || thr->jobs) return 0;

	if (verbose)
	  sfprintf(sfstderr,"delete_thread(%p:%s/%s) (thg=%p) jobs=%d\n",
		   thr,thr->channel,thr->host,thg, thr->jobs);

	free(thr->channel);
	free(thr->host);

	/* Unlink us from the thread time-chain */
	/* ... and thread-group-ring */
	_thread_timechain_unlink(thr);

memset(thr, 0x55, sizeof(*thr));

	free(thr);
	return 1;
}

#if 0 /* Dead code.. */
static void _thread_linkfront __((struct thread *, struct vertex *, struct vertex *));
static void _thread_linkfront(thr,ap,vp)
struct thread *thr;
struct vertex *ap, *vp;
{
	/* Link the VP in front of AP */
	vp->previtem = ap->previtem;
	if (ap->previtem != NULL)
	  ap->previtem->nextitem = vp;
	ap->previtem = vp;
	vp->nextitem = ap;
	if (ap == thr->thvertices)
	  thr->thvertices = vp;
	vp->thread = thr;
}
#endif

/* the  _thread_linktail()  links a vertex into thread */
static void _thread_linktail __((struct thread *, struct vertex *));

static void _thread_linktail(thr,vp)
struct thread *thr;
struct vertex *vp;
{
	if (thr->thvertices != NULL) {
	  thr->lastthvertex->nextitem = vp;
	  vp->previtem    = thr->lastthvertex;
	} else {
	  thr->thvertices = vp;
	  vp->previtem    = NULL;
	}
	vp->nextitem      = NULL;
	vp->thread        = thr;
	thr->lastthvertex = vp;
}

void thread_linkin(vp,cep,cfgid, ce_fillin)
struct vertex *vp;
struct config_entry *cep;
int cfgid;
void (*ce_fillin) __((struct threadgroup*, struct config_entry *));
{
	struct threadgroup *thg;
	struct thread *thr;

	/* int matched = 0; */
	int thg_once;

	struct web *wc = vp->orig[L_CHANNEL];
	struct web *wh = vp->orig[L_HOST];

	mytime(&now);

	if (verbose)
	  sfprintf(sfstderr,"thread_linkin([%s/%s],%s/%d/%s,%d)\n",
		   wc->name, wh->name, cep->channel,
		   cep->flags & CFG_WITHHOST, cep->host, cfgid);

	/* char const *vp_chan = wc->name; */
	/* char const *vp_host = wh->name; */

	if (thrg_root == NULL)
	  create_threadgroup(cep,wc,wh,cep->flags & CFG_WITHHOST,ce_fillin);

	/*
	 *  Search for matching config-entry, AND matching channel,
	 *  AND matching host (depending how the thread-group formation
	 *  is allowed to happen..)
	 *
	 */
	for (thg = thrg_root, thg_once = 1;
	     thg && (thg_once || thg != thrg_root);
	     thg = thg->nextthg, thg_once = 0) {

	  int thr_once;

	  if (thg->cep != cep)	/* Config entries don't match */
	    continue;

	  if (thg->wchan != wc)	/* Channels don't match */
	    continue;

	  if (thg->withhost) {
	    if (thg->whost != wh) /* Tough, must have host match! */
	      continue;
	  }
	  
	  /* The config-entry matches, we have changes to match group */

	  for (thr = thg->thread, thr_once = 1;
	       thr && (thr_once || (thr != thg->thread));
	       thr = thr->nextthg, thr_once = 0) {

#if 0
	    if (!thr->vertex) abort();	/* No vertices ?? */

	    /* no need ? (Channels within a group are identical..) */
	    if (wc != thr->wchan)  abort();
#endif
	    /* Nice! What about host ? */
	    if (wh != thr->whost)  continue;
	    
	    /* We have matching channel, AND matching host */

	    /* Link the vertex into this thread! */

	    if (verbose)
	      sfprintf(sfstderr,"thread_linkin() to thg=%p[%s/%d/%s]; added into existing thread [%s/%s] thr->jobs=%d\n",
		       thg,cep->channel,thg->withhost,cep->host,
		       wc->name,wh->name,thr->jobs+1);

	    _thread_linktail(thr,vp);
	    vp->thgrp   = thg;
	    thr->jobs  += 1;

	    if (thr->proc)     /* Caring about the UF count while running */
	      thr->unfed += 1;

	    if (thr->proc && (thr->nextfeed == NULL)) {
	      /* It is running, but no nextfeed is set (anymore),
		 tackle this vertex into the tail */

	      thr->nextfeed = vp;
	    }

	    /* Hookay..  Try to start it too... */
	    thread_start_(thr);

	    return;
	  }

	  /* No matching thread, however this GROUP matches (or does it?) */

	  /* Add a new thread into this group */
	  thr = create_thread(thg,vp,cep);
	  vp->thgrp = thg;

	  if (verbose)
	    sfprintf(sfstderr,"thread_linkin() to thg=%p[%s/%d/%s]; created a new thread %p [%s/%s]\n",
		     thg,cep->channel,thg->withhost,cep->host,
		     thr,wc->name,wh->name);

	  /* Try to start it too */
	  thread_start_(thr);

	  return;
	}

	/* Add a new group - and its thread .. */
	thg = create_threadgroup(cep, wc, wh, cep->flags & CFG_WITHHOST, ce_fillin);
	thr = create_thread(thg,vp,cep);
	vp->thgrp = thg;

	/* Try to start it too */
	thread_start_(thr);
}

struct web *
web_findcreate(flag, s)
int flag;
const char *s;
{
	struct spblk *spl;
	struct web *wp;
	spkey_t spk;

	/* caller has done 'strlower()' to our input.. */

	spk = symbol_db(s, spt_mesh[flag]->symbols);
	spl = sp_lookup(spk, spt_mesh[flag]);
	if (spl == NULL || (wp = (struct web *)spl->data) == NULL) {
	  /* Not found, create it */
	  wp = (struct web *)emalloc(sizeof (struct web));
	  memset((void*)wp, 0, sizeof (struct web));
	  sp_install(spk, (void *)wp, 0, spt_mesh[flag]);
	  wp->name     = strsave(s);
	  wp->kids     = 0;
	  wp->link     = NULL;
	  wp->linkcnt  = 0;
	}
	if (spl != NULL)
	  wp = (struct web*)spl->data;

	return wp;
}


/*
 * Deallocate a web entry (host or channel vertex header structure).
 */

void
unweb(flag, wp)
int flag;
	struct web *wp;
{
	struct spblk *spl = NULL;
	spkey_t spk;

if (verbose)
  sfprintf(sfstderr,"unweb(flag=%d wp=%p); linkcnt=%d kids=%d\n",
	   flag,wp,wp->kids,wp->linkcnt);

	if (wp->linkcnt > 0)	/* Yet objects holding it */
	  return;
	if (wp->kids > 0)	/* too early to actually remove it */
	  return;

	spk = symbol_lookup_db((u_char *)wp->name, spt_mesh[flag]->symbols);
	if ((spkey_t)0 == spk)	/* Not in the symbol table */
	  return;
	spl = sp_lookup(spk, spt_mesh[flag]);
	if (spl != NULL)	/* Should always have this ... */
	  sp_delete(spl, spt_mesh[flag]);
	symbol_free_db((u_char *)wp->name, spt_mesh[flag]->symbols);
	free(wp->name);

memset(wp, 0x55, sizeof(*wp));

	free((char *)wp);
}


/*
 * unthread(vtx) -- detach this vertex from its thread
 */
static void unthread __((struct thread *thr, struct vertex *vtx));
static void unthread(thr, vtx)
     struct thread *thr;
     struct vertex *vtx;
{
	if (vtx->previtem != NULL)
	  vtx->previtem->nextitem = vtx->nextitem;
	if (vtx->nextitem != NULL)
	  vtx->nextitem->previtem = vtx->previtem;

	if (thr) {
	  thr->jobs                        -= 1;

	  if (thr->nextfeed     == vtx)
	    thr->nextfeed       = thr->nextfeed->nextitem;
	  if (thr->thvertices   == vtx)
	    thr->thvertices     = vtx->nextitem;
	  if (thr->lastthvertex == vtx)
	    thr->lastthvertex   = vtx->previtem;
	}

	vtx->nextitem = NULL;
	vtx->previtem = NULL;
}

/*
 * Detach the vertex from its chains
 *
 * If here is a process, limbo it!
 */
void
web_detangle(vp, ok)
	struct vertex *vp;
	int ok;
{
	/* If it was in processing, remove process node binding.
	   We do this only when we have reaped the channel program. */

	struct thread *thr = vp->thread;

	/* unthread() will also unpick the  nextfeed link.. */

	unthread(thr, vp);

	/* The thread can now be EMPTY! */

	if (thr && (thr->thvertices == NULL))
	  delete_thread(thr);
}

static int vtx_mtime_cmp __((const void *, const void *));
static int vtx_mtime_cmp(ap, bp)
     const void *ap, *bp;
{
	const struct vertex **a = (const struct vertex **)ap;
	const struct vertex **b = (const struct vertex **)bp;

	if ((*a)->cfp->mtime < (*b)->cfp->mtime)
	  return -1;
	else if ((*a)->cfp->mtime > (*b)->cfp->mtime)
	  return 1;
	/* else */

	if ((*a)->cfp->mtimens < (*b)->cfp->mtimens)
	  return -1;
	else if ((*a)->cfp->mtimens > (*b)->cfp->mtimens)
	  return 1;
	/* else */

	return 0;
}


static void
thread_vertex_shuffle(thr)
struct thread *thr;
{
	register struct vertex *vp;
	register int n, i, ni;
	static u_int           ur_size = 0;
	static struct vertex **ur_arr  = NULL;

	/* Randomize the order of vertices in processing, OR
	   sort them by spool-file MTIME, if the thread has
	   AGEORDER -flag set. */

	/* 1) Create storage array for the vertex re-arrange */
	if (ur_size == 0) {
	  ur_size = 100;
	  ur_arr = (struct vertex **)
	    emalloc(ur_size * sizeof (struct vertex *));
	}
	/* 2) Store the vertices into a re-arrange array (and count) */
	for (n = 0, vp = thr->thvertices; vp != NULL; vp = vp->nextitem) {
	  if (n >= ur_size) {
	    ur_size *= 2;
	    ur_arr = (struct vertex **)realloc((char *)ur_arr,
					       ur_size *
					       sizeof (struct vertex *));
	  }
	  ur_arr[n++] = vp;
	}

	/* 3) re-arrange pointers */
	if (thr->thgrp->ce.flags & CFG_AGEORDER) {
	  /* mtime order */
	  if (n > 1)
	    qsort((void*)ur_arr, n, sizeof(struct vertex *), vtx_mtime_cmp);
	} else
	  /* Random order */
	  for (i = 0; i < n; ++i) {
	    ni = ranny(n-1);
	    vp = ur_arr[i];
	    ur_arr[i] = ur_arr[ni];
	    ur_arr[ni] = vp;
	  }
	/* 4) Relink previtem/nextitem pointers */
	for (i = 0; i < n; ++i) {
	  if (i > 0)
	    ur_arr[i]->previtem = ur_arr[i-1];
	  if (i < (n-1))
	    ur_arr[i]->nextitem = ur_arr[i+1];
#if 0 /* this variable is no longer existing */
	  /* 4c) Clear wakeup timer; the feed_child() will refuse
	     to feed us, if this one is not cleared.. */
	  ur_arr[i]->wakeup = 0;
#endif
	}
	ur_arr[  0]->previtem = NULL;
	ur_arr[n-1]->nextitem = NULL;
	/* 5) Finish the re-arrangement by saving the head,
	      and tail pointers */
	thr->thvertices   = ur_arr[  0];
	thr->nextfeed     = ur_arr[  0];
	thr->lastthvertex = ur_arr[n-1];
	thr->unfed = n;
}

static int
thread_start_(thr)
     struct thread *thr;
{
	struct config_entry *ce = &(thr->thgrp->ce);

	if (thr->proc != NULL) {
	  /* There is *somebody* active!  Shall we start, or not ? */
	  if (ce->flags & CFG_WAKEUPRESTARTONLY)
	    return 0;
	}

	return thread_start(thr, 0);
}


/*
 * thread_start() -- start the thread, if:
 *   - if the thread is not already running
 *   - thread-group has idle processor (feed immediately)
 *   - if no resource limits are exceeded for starting it
 *
 * Return non-zero, if did start something.
 */

int
thread_start(thr, queueonly_too)
     struct thread *thr;
     int queueonly_too;
{
	int rc;
	struct vertex      *vp  = thr->thvertices;
	struct threadgroup *thg = thr->thgrp;
	struct config_entry *ce = &(thr->thgrp->ce);
	struct web         *ho;
	struct web         *ch;

	queryipccheck();

	if (!thr->thrkids && !thr->jobs) {
	  /* Cleanup when no processes, nor vertices */
	  delete_thread(thr);
	  return 0;
	}

	if (syncstart || (freeze && !slow_shutdown)) return 0;
	if (!queueonly_too && (ce->flags & CFG_QUEUEONLY)) return 0;

	ho = vp->orig[L_HOST];
	ch = vp->orig[L_CHANNEL];

	if (procselect) {
	  thr->pending = "procsel-mismatch";
	  if (*procselect != '*' &&
	      strcmp(procselect,ch->name) != 0)
	    return 0;
	  if (*procselhost != '*' &&
	      strcmp(procselhost,ho->name) != 0)
	    return 0;
	}
	thr->pending = NULL;

	if (verbose)
	  sfprintf(sfstderr,"thread_start(thr=%s/%d/%s) (dt=%d thr=%p jobs=%d)\n",
		   ch->name, thg->withhost, ho->name, (int)(thr->wakeup-now),
		   thr, thr->jobs);

	if ((thr->thrkids >= ce->maxkidThread) ||
	    /* FIXME: real unfed count ? */
	    (thr->proc && (thr->thrkids >= thr->unfed))) {
	  if (verbose) {
	    struct procinfo * proc = thr->proc;
	    sfprintf(sfstderr," -- already running; thrkids=%d jobs=%d procs={ %p",
		     thr->thrkids, thr->jobs, proc);
	    proc = proc->pnext;
	    while (proc) {
	      sfprintf(sfstderr, " %p", proc);
	      proc = proc->pnext;
	    }
	    sfprintf(sfstderr, " }\n");
	  }
	  return 0; /* Already running */
	}

      re_pick:
	if (thg->idleproc) {
	  struct procinfo *proc;

	  /* There is at least one.. */
	  proc = thg->idleproc;

	  /* Idle processor(s) exists, try to optimize by finding
	     an idle proc with matching channel & host from previous
	     activity. If not found, pick any with matching CHANNEL,
	     unless must have also matching HOST... */

	  for (; proc && (proc->ho != ho || proc->ch != ch); proc = proc->pnext) ;
	  if (!proc && !thg->withhost) {
	    /* None of the previous ones matched, pick with matching CHANNEL,
	       HOST is allowed to wild-card.. */
	    proc = thg->idleproc;
	    for (; proc && (proc->ch != ch); proc = proc->pnext) ;
	  }
	  if (!proc)
	    goto create_new;

	  /* Selected one of them.. */

	  /* Is this idle chain leader?   Set pnext as new leader */
	  if (thg->idleproc == proc) thg->idleproc = proc->pnext;
	  /* Unlink from idle proc chain */
	  if (proc->pprev) proc->pprev->pnext = proc->pnext;
	  if (proc->pnext) proc->pnext->pprev = proc->pprev;
	  proc->pnext = proc->pprev   = NULL;

	  thg->idlecnt -= 1;

	  --idleprocs;

	  /* Move to ACTIVE state */
	  MIBMtaEntry->sc.TransportAgentsActiveSc += 1;
	  MIBMtaEntry->sc.TransportAgentsIdleSc   -= 1;

	  
	  /* It may be that while we idled it, it died at the idle queue.. */
	  if (proc->pid <= 0 || proc->tofd < 0) {

	    /* sfprintf(sfstderr,
	       "%% thread_start(thr=%s/%d/%s) (proc=%p ->pid=%d ->tofd=%d)\n",
	       ch->name, thg->withhost, ho->name, proc,
	       proc->pid, proc->tofd); */

	    goto re_pick;
	  }

	  /* Thread-groups are made such that here at thread_start() we
	     can always switch over in between threads */

	  if (proc->ho != NULL && proc->ho != ho) {
	    /* Get rid of the old host web */
	    proc->ho->kids -= 1;
	    unweb(L_HOST,proc->ho);
	    proc->ho = NULL;
	  }

	  /* Move the kid to this host web */
	    
	  if (proc->ho != ho) {
	    proc->ho = ho;
	    proc->ho->kids += 1;
	  }

	  /* In theory the CHANNEL could be different -- in practice NOT! */
	  proc->ch = ch;

	  /* MULTI-TA-PER-THREAD -- only the first proc inits feed-state */
	  if (! thr->proc ) {

	    /* Randomize the order of thread vertices
	       (or sort by spool file mtime, if in AGEORDER..) */
	    /* Also init thr->nextfeed */
	    thread_vertex_shuffle(thr);
	  }

	  /* Its idle process, feed it! */

	  proc->state   = CFSTATE_LARVA;
	  proc->overfed = 1; /* A simulated state.. */

	  proc->pthread = thr;

	  if (thr->proc)   proc->pnext = thr->proc;
	  if (proc->pnext) proc->pnext->pprev = proc;
	  if (proc->pprev) proc->pprev->pnext = proc;

	  thr->proc     = proc;
	  thr->thrkids += 1;

	  if (verbose)
	    sfprintf(sfstderr, "%% thread_start(thr=%s/%d/%s) (proc=%p dt=%d thr=%p jobs=%d)\n",
		     ch->name, thg->withhost, ho->name, thr->proc,
		     (int)(thr->wakeup-now), thr, thr->jobs);

	  ta_hungry(proc);

	  return 1;
	}

 create_new:

	/* Check resource limits - MaxTa, MaxChan, MaxThrGrpTa */
	/* If resources are exceeded, reschedule.. */

	vp = thr->thvertices;

	if (numkids >= ce->maxkids) {
	  vp->ce_pending = SIZE_L;
	  thr->pending = ">MaxTA";
	} else if (vp->orig[L_CHANNEL]->kids >= ce->maxkidChannel) {
	  vp->ce_pending = L_CHANNEL;
	  thr->pending = ">MaxChannel";
	} else if (thg->transporters >= ce->maxkidThreads) {
	  vp->ce_pending = L_HOST;
	  thr->pending = ">MaxRing";
	} else if (thr->thrkids >= ce->maxkidThread) {
	  vp->ce_pending = SIZE_L;
	  thr->pending = ">MaxThr";
	} else {
	  vp->ce_pending = 0;
	  thr->pending = NULL;
	}

	if (vp->ce_pending) {
	  if (verbose)
	    sfprintf(sfstderr,"%s: (%d %dC %dT %dTh) >= (%d %dC %dT %dTh)\n",
		     ce->command,
		     numkids,
		     vp->orig[L_CHANNEL]->kids,
		     thg->transporters,
		     thr->thrkids,
		     ce->maxkids,
		     ce->maxkidChannel,
		     ce->maxkidThreads,
		     ce->maxkidThread);
	  /*
	   * Would go over limit.  Rescheduling for the next
	   * (single) interval works ok in many situation.
	   * However when the scheduler is very busy one can
	   * run into systemic problems with some set of messages
	   * blocking another set of messages.  The only way
	   * around that is a roundrobin scheme, implemented
	   * by the fifo nature of the thread scheduling.
	   */
	  reschedule(vp, 0, -1);
	  return 0;
	}

	/* Now we are ready to start a new child to run our bits */
	
	if (! thr->proc ) {
	  /* MULTI-TA-PER-THREAD -- first proc inits the feed-state */

	  /* Randomize the order of thread vertices
	     (or sort by spool file mtime, if in AGEORDER..) */
	  /* Also init thr->nextfeed */
	  thread_vertex_shuffle(thr);
	}

	rc = start_child(thr->thvertices,
			 thr->thvertices->orig[L_CHANNEL],
			 thr->thvertices->orig[L_HOST]);

	if (thr->proc && verbose)
	  sfprintf(sfstderr,"%% thread_start(thr=%s/%d/%s) (proc=%p dt=%d thr=%p jobs=%d)\n",
		   ch->name, thg->withhost, ho->name, thr->proc,
		   (int)(thr->wakeup-now), thr, thr->jobs);


	return rc;
}


/*
 * pick_next_vertex() -- pick next free to process vertex in this thread
 *
 * This is called *only* by  feed_child(), and  proc->vertex  directs
 * then the caller of feed_child() to tune the process state.
 * (From STUFFING to FINISHING and possibly to IDLE.)
 * 
 * - if (proc->pthread->nextfeed != NULL) ...nextfeed = ...nextfeed->nextitem;
 * - return (...nextfeed != NULL);
 *
 */

/* Return 0 for errors, 1 for success; result is at  ...nextfeed */

int
pick_next_vertex(proc)
     struct procinfo *proc;
{
	struct thread * thr = proc->pthread;
	struct vertex * vtx = NULL;

	if (thr) vtx = thr->nextfeed;

	if (verbose)
	  sfprintf(sfstderr,"pick_next_vertex(proc=%p) proc->tofd=%d, thr=%p, pvtx=%p, jobs=%d OF=%d S=%s\n",
		   proc, proc->tofd, thr, vtx, thr ? thr->jobs : 0,
		   proc->overfed, proc_state_names[proc->state]);

	if (proc->pid < 0 || proc->tofd < 0) {	/* "He is dead, Jim!"	*/
	  if (verbose) sfprintf(sfstderr," ... NONE, 'He is dead, Jim!'\n");
	  return 0;
	}

	if (vtx) /* Pick next item */
	  thr->nextfeed = vtx = vtx->nextitem;

	return (vtx != NULL);
}

/*
 *  The  thread_expire2()  will handle exceedingly old things
 *  with ages in excess of expire+expire2 (seconds) in queue
 *  even if no successfull delivery attempt has been made.
 *
 *  Return the kill-count.
 *
 *  Side-effect warning: 
 *         Afterwards the THR may point to nonexistent object!
 */


int
thread_expire2(thr, timelimit, killall, msgstr)
     struct thread *thr;
     time_t timelimit;
     int killall;	  /* later uses in mind.. now dummy parameter */
     const char *msgstr;  /* ... likewise. */
{
	int killcount = 0;
	struct vertex       *vtx  = thr->thvertices;
	struct vertex	*nextvtx;

	for ( ;vtx; vtx = nextvtx) {
	  int expire_this = 0;

	  nextvtx = vtx->nextitem;

	  /* Time to expire ? */
	  if (vtx->ce_expiry > 0 && vtx->ce_expiry <= now &&
	      vtx->attempts  > 0) {
	    expire_this = 1;
	  }
	  if (vtx->ce_expiry2 > 0 && vtx->ce_expiry2 <= now) {
	    expire_this = 1;
	  }
	  if (expire_this) {
	    /* ... and now expire it! */
	    /* this MAY invalidate also the THREAD object! */

	    expire(vtx, -1); /* ... them all. */
	    ++killcount;

	    mytime(&now);
	    if (now > timelimit) break;
	  }
	}

	return killcount;
}


/*
 * The  thread_reschedule()  updates threads time-chain to match the
 * new value of wakeup for the  doagenda()  to later use.
 * Return 0 for DESTROYED thread, 1 for EXISTING thread.
 */

int
thread_reschedule(thr, retrytime, index)
     struct thread *thr;
     int index;
     time_t retrytime;
{
	struct vertex *vtx = thr->thvertices;
	struct vertex *nvtx;
	time_t wakeup = 0;

	if (verbose)
	  sfprintf(sfstderr,"thread_reschedule() ch=%s ho=%s jobs=%d thr=%p proc=%p\n",
		   thr->channel,thr->host,thr->jobs,thr,thr->proc);


	if (!thr->thrkids && !thr->jobs) {
	  delete_thread(thr);
	  return 0;
	}

	/* If there are multiple kids working still, DON'T reschedule! */
	if ((thr->thrkids > 0)  ||  (vtx == NULL)) return 1;

	/* find out when to retry */
	mytime(&now);

	/* if we are already scheduled for the future, don't reschedule */
	if (thr->wakeup > now) {
	  /* thr->wakeup = vtx->wakeup; */
	  if (verbose)
	    sfprintf(sfstderr,"...prescheduled\n");
	  goto timechain_handling;
	}

	if (thr->thgrp->ce.nretries <= 0) {
	  if (verbose)
	    sfprintf(sfstderr,"...ce->retries = %d\n", vtx->thgrp->ce.nretries);
	  goto timechain_handling;
	}

	if (thr->retryindex >= thr->thgrp->ce.nretries) {
	  if (thr->thgrp->ce.nretries > 1)
	    thr->retryindex = ranny(thr->thgrp->ce.nretries-1);
	  else
	    thr->retryindex = 0;
	}


	/*
	 * clamp retry time to a predictable interval so we
	 * eventually bunch up deliveries.
	 */
	if (retrytime > 100000 && retrytime < now+63) {
	  thr->wakeup = now;
	  /* goto timechain_handling ??? */
	}

	thr->wakeup += thr->thgrp->ce.retries[thr->retryindex] * thr->thgrp->ce.interval;
	thr->retryindex++;

	wakeup = thr->wakeup;

	thr->retryindex++;

	/* If history, move forward by ``ce.interval'' multiple */
	if (thr->wakeup < now)
	  thr->wakeup += ((((now - thr->wakeup) / thr->thgrp->ce.interval)+1)
			  * thr->thgrp->ce.interval);

	wakeup = thr->wakeup;


	if (retrytime < now+63)
	  retrytime = wakeup;

	/* Reschedule ALL vertices on this thread */
	for ( ;vtx; vtx = nvtx) {
	  int expire_this = 0;

	  nvtx = vtx->nextitem;

	  /* Time to expire ? */
	  if (vtx->ce_expiry > 0 && vtx->ce_expiry <= now &&
	      vtx->attempts  > 0) {
	    expire_this = 1;
	  }
	  if (vtx->ce_expiry2 > 0 && vtx->ce_expiry2 <= now) {
	    expire_this = 1;
	  }
	  if (expire_this) {
	    /* ... and now expire it! */
	    /* this MAY invalidate also the THREAD object! */

	    if (thr->jobs > 1) {
	      expire(vtx, index);
	    } else {
	      expire(vtx, index);
	      thr = NULL; /* The THR-pointed object is now invalid */
	    }
	    continue;
	  }

	  /* Didn't expire, so time to tune the wakeup ... */

#if 0
	  if (vtx->wakeup < retrytime)
	    vtx->wakeup = retrytime;
	  if (wakeup > vtx->wakeup || wakeup == 0)
	    wakeup = vtx->wakeup;
#endif
	}

#if 0
	if (thr != NULL)
	  thr->wakeup = wakeup;
#endif

 timechain_handling:
	/* In every case the rescheduling means we move this thread
	   to the end of the thread_head chain.. */

	if (thr != NULL) {
	  _thread_timechain_unlink(thr);
	  _thread_timechain_append(thr);
	}

	return (thr != NULL);
}


/*
 * reschedule() operates WITHIN a thread, but does *not* move things!
 *
 */

void
reschedule(vp, factor, index)
	struct vertex *vp;
	int factor, index;
{
	int skew;
	struct thread *thr = vp->thread;
	struct threadgroup *thg = vp->thgrp;
	struct config_entry *ce = &(thg->ce);

	/* Hmm.. The reschedule() is called only when we have a reason
	   to call it, doesn't it ?  */

	/* find out when to retry */
	mytime(&now);

	if (verbose)
	  sfprintf(sfstderr,"reschedule %p now %d expiry in %d attempts %d factor %d inum %d (%s/%s: %s)\n",
		   vp, (int)now,
		   (int)((vp->ce_expiry > 0) ? (vp->ce_expiry - now) : -999),
		   vp->attempts,
		   factor, (int)(vp->cfp->id),
		   vp->orig[L_CHANNEL]->name,
		   vp->orig[L_HOST]->name,
		   vp->cfp->mid);
	/* if we are already scheduled for the future, don't reschedule */
	if (thr->wakeup > now) {
	  if (verbose)
	    sfprintf(sfstderr,"prescheduled\n");
	  return;
	}

	if (ce->nretries <= 0) {
	  if (verbose)
	    sfprintf(sfstderr,"ce->retries = %d\n", ce->nretries);
	  return;
	}
	if (factor == -1 && vp->attempts) {
	  if (thr->retryindex >= ce->nretries) {
	    if (ce->nretries > 1)
	      thr->retryindex = ranny(ce->nretries-1);
	    else
	      thr->retryindex = 0;
	  }

	  /*
	   * clamp retry time to a predictable interval so we
	   * eventually bunch up deliveries.
	   */
	  skew = thr->wakeup % ce->interval;
	  if (skew <= ce->interval / 2)
	    skew = - (skew + (ce->skew - 1));
	  else
	    skew = skew + (ce->skew - 1);
	  skew = skew / ce->skew; /* want int div truncation */

	  thr->wakeup += (skew +
			  ce->retries[thr->retryindex] * ce->interval);
	  thr->retryindex++;
	} else if (factor < -1) {
	  thr->wakeup = -factor;
	} else
	  thr->wakeup += factor * ce->interval;

	/* I THINK there could be an assert that if this happens,
	   something is WRONG.. */
	if (vp->attempts == 0)
	  thr->wakeup = now;

	/* XX: change this to a mod expression */
	if (thr->wakeup < now)
	  thr->wakeup = ((((now - thr->wakeup) / ce->interval)+1)
			 * ce->interval) + 10 /* + 2*thr->jobs */ ;

	/* Makes sure that next future event is at +10+2*jobcount seconds
	   in the future..  A kludge approach, but still.. */

	if (vp->ce_expiry > 0
	    && vp->ce_expiry <= thr->wakeup
	    && vp->attempts > 0) {
	  if (verbose)
	    sfprintf(sfstderr,"ce_expiry = %d, %d attempts\n",
		     (int)(vp->ce_expiry), vp->attempts);

	  /* expire() will delete this vertex in due time */
	  expire(vp, index);

	  return;
	}
}


/*
 * With the  idle_cleanup()  we clean up idle processes, that have
 * been idle for too long (idlemax=nnnns)
 *
 * Because during its progress the thread-groups can disappear,
 * (as is one of its mandates) this code looks a bit peculiar..
 */
int
idle_cleanup()
{
	/* global: time_t now */
	struct threadgroup *thg, *nthg;
	int thg_once;
	int freecount = 0;

	mytime(&now);

	if (verbose) sfprintf(sfstderr,"idle_cleanup()\n");

	if (!thrg_root) return 0; /* No thread group! */

	for (thg = thrg_root, thg_once = 1;
	     thg_once || (thg != thrg_root);
	     thg = nthg, thg_once = 0) {

	  nthg = thg->nextthg;

	  if (thg->thread != NULL) {
	    struct procinfo *p;
	    struct thread *thr, *nthr;
	    int thr_once;
	    
	    /* Clean-up faulty client  --  KLUDGE :-(  --  OF=0, HA > much */

	    for (thr = thg->thread, thr_once = 1;
		 thr && (thr_once || (thr != thg->thread));
		 thr = nthr, thr_once = 0) {

	      nthr = thr->nextthg;

	      p = thr->proc;
	      if (thr->thgrp != thg) /* Not of this group ? */
		continue; /* Next! */
	      if (!p) /* No process */
		continue;
	      if ((p->cmdlen == 0) && (p->overfed == 0) && (p->tofd >= 0) &&
		  (p->hungertime != 0) && (p->hungertime + MAX_HUNGER_AGE <= now)) {

		/* Close the command channel, let it die itself.
		   Rest of the cleanup happens via mux() service. */
		if (verbose)
		  sfprintf(sfstderr,"idle_cleanup() killing TA on tofd=%d pid=%d\n",
			 p->tofd, (int)p->pid);

		thr->wakeup = now-1; /* reschedule immediately! */

		write(p->tofd,"\n",1); /* XXXX: should this be removed ?? */

		pipes_shutdown_child(p->tofd);
		p->tofd = -1;

		++freecount;

		/* Reclaim will (in due time) detect dead child, and
		   decrement child counters. */

		zsyslog((LOG_ERR, "ZMailer scheduler kludge shutdown of TA channel (info for debug only); %s/%s/%d HA=%ds",
			 thr->channel, thr->host, thr->thgrp->withhost,
			 (int)(now - p->hungertime)));
	      }
	    }
	  }

	  if (thg->idleproc) {
	    struct procinfo *p;
	    
	    for (p = thg->idleproc; p != NULL; p = p->pnext) {

	      if ((thg->cep->idlemax + p->hungertime < now) &&
		  (p->cmdlen == 0) && (p->tofd >= 0)) {
		/* It is old enough -- ancient, one might say.. */

		/* Close the command channel, let it die itself.
		   Rest of the cleanup happens via mux() service. */
		if (verbose)
		  sfprintf(sfstderr,"idle_cleanup() killing TA on tofd=%d pid=%d\n",
			   p->tofd, (int)p->pid);
		write(p->tofd,"\n",1);
		pipes_shutdown_child(p->tofd);
		p->tofd       = -1;
		++freecount;
	      }
	    }
	  }
	  /* If there are no threads, nor transporters, delete the thg */
	  delete_threadgroup(thg);
	}
	return freecount;
}

static time_t oldest_age_on_thread __((struct thread *));
static time_t oldest_age_on_thread(th) /* returns the AGE in seconds.. */
struct thread *th;
{
	register time_t oo = now+1;
	register struct vertex *vp;

	vp = th->thvertices;
	while (vp) {
	  if (vp->cfp->mtime < oo)
	    oo = vp->cfp->mtime;
	  vp = vp->nextitem;
	}
	return (now - oo);
}

static void _thread_detail_detail(fp, mqmode, thr, thrkidsump, procsp)
     Sfio_t *fp;
     int mqmode, *thrkidsump, *procsp;
     struct thread *thr;
{
	int spc = (mqmode & MQ2MODE_FULL) ? ' ' : '\t';


	if (mqmode & MQ2MODE_FULL)
	  sfprintf(fp,"N=%-3d R=%-3d A=%-2d", thr->jobs, thr->rcpts, thr->attempts);
	if (mqmode & MQ2MODE_FULL2)
	  sfprintf(fp,"N=%d\tR=%d\tA=%d", thr->jobs, thr->rcpts, thr->attempts);
	
	if (thr->proc != NULL &&
	    thr->proc->pthread == thr) {
	  
	  int thrprocs = 0;
	  struct procinfo *proc;

	  for (proc = thr->proc; proc; proc = proc->pnext) {
	    ++thrprocs;
	    if (procsp)     *procsp     += 1;
	    if (thrkidsump) *thrkidsump += 1;
	  }

	  if (mqmode & (MQ2MODE_FULL|MQ2MODE_FULL2)) {
	    if (thr->thrkids != thrprocs)
	      sfprintf(fp, "%cKids=%d/%d", spc, thr->thrkids, thrprocs);

	    sfprintf(fp, "%cP={", spc);
	    for (proc = thr->proc; proc ; proc = proc->pnext) {
	      sfprintf(fp, "%d", (int)proc->pid);
	      if (proc->pnext) sfprintf(fp, ",");
	    }
	    sfprintf(fp, "}");

	    sfprintf(fp, "%cHA={", spc);
	    for (proc = thr->proc; proc ; proc = proc->pnext) {
	      sfprintf(fp, "%d", (int)(now - proc->hungertime));
	      if (proc->pnext) sfprintf(fp, ",");
	    }
	    sfprintf(fp, "}s");

	    sfprintf(fp, "%cFA={", spc);
	    for (proc = thr->proc; proc ; proc = proc->pnext) {
	      if (proc->feedtime == 0)
		sfprintf(fp, "never");
	      else
		sfprintf(fp, "%d", (int)(now - proc->feedtime));
	      if (proc->pnext) sfprintf(fp, ",");
	    }
	    sfprintf(fp, "}s");

	    sfprintf(fp, "%cOF={", spc);
	    for (proc = thr->proc; proc ; proc = proc->pnext) {
	      sfprintf(fp, "%d", proc->overfed);
	      if (proc->pnext) sfprintf(fp, ",");
	    }
	    sfprintf(fp, "}");

	    sfprintf(fp, "%cS={", spc);
	    for (proc = thr->proc; proc ; proc = proc->pnext) {
	      sfprintf(fp, "%s", proc_state_names[proc->state]);
	      if (proc->pnext) sfprintf(fp, ",");
	    }
	    sfprintf(fp, "}");

	    sfprintf(fp, "%cUF=%d", spc, thr->unfed);
	  }

	} else if (thr->wakeup > now) {
	  if (mqmode & (MQ2MODE_FULL|MQ2MODE_FULL2)) {
	    sfprintf(fp,"%cW=%ds", spc, (int)(thr->wakeup - now));
	  }
	} else if (thr->pending) {
	  if (mqmode & (MQ2MODE_FULL|MQ2MODE_FULL2)) {
	    sfprintf(fp,"%cpend=%s", spc, thr->pending);
	  }
	}

	if (mqmode & (MQ2MODE_FULL|MQ2MODE_FULL2)) {
	  char timebuf[20];
	  *timebuf = 0;
	  saytime((long)oldest_age_on_thread(thr), timebuf, 1);
	  sfprintf(fp, "%cQA=%s", spc, timebuf);

	  if (thr->thvertices && thr->thvertices->ce_pending)
	    if (thr->thvertices->ce_pending != SIZE_L && spc == ' ')
	      sfprintf(fp, "%s",
		       (thr->thvertices->ce_pending ==
			L_CHANNEL ? " channelwait" : " threadwait"));
	  sfprintf(fp, "\n");
	}
}

/* The  "SHOW THREADS"  diagnostic tool */
void thread_report(fp,mqmode)
     Sfio_t *fp;
     int mqmode;
{
	struct threadgroup *thg;
	int thg_once = 1;
	int jobsum = 0, jobtotal = 0;
	int threadsum = 0;
	char timebuf[20];

	int width;
	int cnt, procs, thrkidsum;
	int rcptsum = 0;
	struct procinfo *p;
	struct thread *thr;

	mytime(&now);

#if 0
	if (thrg_root == NULL) {
	  *timebuf = 0;
	  saytime((long)(now - sched_starttime), timebuf, 1);
	  sfprintf(fp,"No threads/processes.  Uptime: %s\n",timebuf);
	  return;
	}
#endif

	for (thg = thrg_root;
	     thg && (thg_once || thg != thrg_root);
	     thg = thg->nextthg) {

	  int thr_once;

	  thg_once = 0;
	  if (mqmode & (MQ2MODE_FULL | MQ2MODE_QQ)) {
	    sfprintf(fp,"%s/%s/%d\n",
		     thg->cep->channel, thg->cep->host, thg->withhost);
	  }

	  cnt   = 0;
	  procs = 0;
	  jobsum = 0;
	  thrkidsum = 0;

#if 1 /* XX: zero for verifying of modified system; turn to 1 for running! */

	  /* We scan thru the local ring of threads */

	  for (thr = thg->thread, thr_once = 1;
	       thr && (thr_once || (thr != thg->thread));
	       thr = thr->nextthg, thr_once = 0)
#else
	  /* We scan there in start order from the  thread_head
	     chain! */

	  for (thr = thread_head;
	       thr != NULL;
	       thr = thr->nexttr)
#endif
	  {
	    if (thr->thgrp != thg) /* Not of this group ? */
	      continue; /* Next! */

	    {
	      struct vertex *vp = thr->thvertices;
	      while (vp != NULL) {
		rcptsum += vp->ngroup;
		vp = vp->nextitem;
	      }
	    }

	    if (mqmode & MQ2MODE_FULL2) {
	      width = sfprintf(fp,"%s\t%s\t",
			       /* thr->thvertices->orig[L_CHANNEL]->name */
			       thr->channel,
			       /* thr->thvertices->orig[L_HOST]->name */
			       thr->host);
	    } else if (mqmode & MQ2MODE_FULL) {
	      width = sfprintf(fp,"    %s/%s/%d",
			       /* thr->thvertices->orig[L_CHANNEL]->name */
			       thr->channel,
			       /* thr->thvertices->orig[L_HOST]->name */
			       thr->host,
			       thr->thgrp->withhost);
	      if (width < 0) break; /* error.. */
	      width += 7;
	      if (width < 16-1)
		sfprintf(fp,"\t");
	      if (width < 24-1)
		sfprintf(fp,"\t");
	      if (width < 32-1)
		sfprintf(fp,"\t");
	      if (width < 40-1)
		sfprintf(fp,"\t");
	      else
		sfprintf(fp," ");
	    }

	    jobsum += thr->jobs;
	    ++cnt;

	    _thread_detail_detail(fp, mqmode, thr, &thrkidsum, &procs);

	  }

	  if (mqmode & (MQ2MODE_FULL | MQ2MODE_QQ)) {

	    sfprintf(fp,"\tThreads: %4d",thg->threads);

	    if (thg->threads != cnt)
	      sfprintf(fp,"/%d",cnt);

	  }

	  cnt = 0;
	  for (p = thg->idleproc; p != 0; p = p->pnext) ++cnt;
	  procs += cnt;

	  if (mqmode & (MQ2MODE_FULL | MQ2MODE_QQ)) {

	    sfprintf(fp, " Msgs: %5d Procs: %3d", jobsum, thg->transporters);

	    if (thg->transporters != procs)
	      sfprintf(fp,"/%d",procs);

	    sfprintf(fp," Idle: %3d",thg->idlecnt);
	    if (thg->idlecnt != cnt)
	      sfprintf(fp, "/%d", cnt);

	    sfprintf(fp, " Plim: %3d Flim: %3d Tlim: %d\n",
		     thg->ce.maxkidThreads, thg->ce.overfeed, thg->ce.maxkidThread);
	  }

	  jobtotal  += jobsum;
	  threadsum += thg->threads;
	}

	if (mqmode & (MQ2MODE_FULL | MQ2MODE_QQ | MQ2MODE_SNMP)) {
	  long files;
	  *timebuf = 0;
	  saytime((long)(now - sched_starttime), timebuf, 1);
	  sfprintf(fp,"Kids: %d  Idle: %2d  Msgs: %3d  Thrds: %3d  Rcpnts: %4d  Uptime: ",
		   numkids, idleprocs, global_wrkcnt, threadsum, jobtotal);
	  if (mqmode & MQ2MODE_SNMP)
	    sfprintf(fp, "%ld sec\n",(long)(now - sched_starttime));
	  else
	    sfprintf(fp, "%s\n",timebuf);

	  sfprintf(fp, "Msgs in %lu out %lu stored %ld ",
		   (u_long)MIBMtaEntry->sc.ReceivedMessagesSc,
		   (u_long)MIBMtaEntry->sc.TransmittedMessagesSc,
		   (long)MIBMtaEntry->sc.StoredMessagesSc);

	  files = thread_count_files();
	  if ((long)MIBMtaEntry->sc.StoredMessagesSc != files)
	    sfprintf(fp, "(%ld) ", files);

	  sfprintf(fp, "Rcpnts in %lu out %lu stored %ld",
		   (u_long)MIBMtaEntry->sc.ReceivedRecipientsSc,
		   (u_long)MIBMtaEntry->sc.TransmittedRecipientsSc,
		   (long)MIBMtaEntry->sc.StoredRecipientsSc);

	  if (rcptsum != MIBMtaEntry->sc.StoredRecipientsSc)
	    sfprintf(fp, " (%d)", rcptsum);

	  sfprintf(fp, "\n");
	}
	sfsync(fp);
}


/* The  "SHOW THREAD channel host"  diagnostic tool */
void thread_detail_report(fp,mqmode,channel,host)
     Sfio_t *fp;
     int mqmode;
     char *channel, *host;
{
	struct thread *th;
	spkey_t spk;
	struct spblk *spl;
	struct web *wh, *wc;
	struct vertex *vp;
	int i;
	char buf[100];

	mytime(&now);

	spk = symbol_lookup_db((void*)channel, spt_mesh[L_CHANNEL]->symbols);
	spl = sp_lookup(spk, spt_mesh[L_CHANNEL]);
	if (spl == NULL || spl->data == NULL) {
	  /* Not found, nothing to do.. */
	  return;
	}
	wc = (struct web *)spl->data;

	spk = symbol_lookup_db((void*)host, spt_mesh[L_HOST]->symbols);
	spl = sp_lookup(spk, spt_mesh[L_HOST]);
	if (spl == NULL || spl->data == NULL) {
	  /* Not found, nothing to do.. */
	  return;
	}
	wh = (struct web *)spl->data;

	for (th = thread_head; th; th = th->nexttr) {
	  if (wh == th->whost && wc == th->wchan) {
	    break;
	  }
	}
	if (th) {
	  /* Found it! */

	  /* First line is MQ2MODE_FULL summary report, rest are detail report */
	  sfprintf(fp, "#%s/%s/%d  ", th->channel, th->host, th->thgrp->withhost);
	  _thread_detail_detail(fp, MQ2MODE_FULL, th, NULL, NULL);

	  /* Now the actual detail report */
	  for (vp = th->thvertices; vp; vp = vp->nextitem) {
	    struct ctlfile *cfp = vp->cfp;
	    for (i = 0; i < vp->ngroup; ++i) {
	      /* Spoolfile */
	      sfprintf(fp, "%s%s   ", cfpdirname(cfp->dirind), cfp->mid);

	      /* How manyth in a group ? */
	      sfprintf(fp, "\t%d", i);
	      /* Sender index -- or sender address */
	      sfprintf(fp, "\t%s", cfp->erroraddr);
	      /* Recipient offset */
	      sfprintf(fp,"\t%d", cfp->offset[vp->index[i]]);
	      /* Expiry stamp */
	      sfprintf(fp,"\t%ld", (long)vp->ce_expiry);
	      /* next wakeup */
	      sfprintf(fp,"\t%ld", (long)th->wakeup);
	      /* last feed time */
	      sfprintf(fp,"\t%ld", (long)vp->lastfeed);
	      /* attempts */
	      sfprintf(fp,"\t%d\t", vp->attempts);
	      /* ce_pending */
	      if (th->wakeup > now) {
		*buf = 0;
		saytime((long)(th->wakeup - now), buf, 1);
		sfprintf(fp,"retry in %s", buf);
	      } else {
		switch(vp->ce_pending) {
		case SIZE_L: /* BAD! */
		  break;
		case L_CHANNEL:
		  sfprintf(fp,"channel");
		  break;
		default:
		  sfprintf(fp,"thread");
		  break;
		}
	      }
	      /* message - if any */
	      sfprintf(fp, "\t");
	      if (vp->message)
		sfprintf(fp,"%s", vp->message);
	      sfprintf(fp, "\n");
	    }
	  }
	}

	sfsync(fp);
}


int thread_count_recipients()
{
	struct threadgroup *thg;
	struct thread *thr;
	int thg_once;
	int jobtotal = 0;

	if (thrg_root == NULL)
	  return 0;

	if (thrg_root)
	  for (thg = thrg_root, thg_once = 1;
	       thg_once || thg != thrg_root;
	       thg = thg->nextthg, thg_once = 0) {

	    int thr_once;
	    int jobsum = 0;

	    if (thg->thread)
	      for (thr = thg->thread, thr_once = 1;
		   thr_once || (thr != thg->thread);
		   thr = thr->nextthg, thr_once = 0) {

		jobsum += thr->jobs;

	      }
	    jobtotal += jobsum;
	  }
	return jobtotal;
}


static int spl_thread_cnt_files __((void *, struct spblk *spl));
static int spl_thread_cnt_files(p, spl)
	void *p;
	struct spblk *spl;
{
	int *ip = p;
	*ip += 1;
	return 0;
}


int thread_count_files __((void))
{
	int thread_files_count = 0;
	sp_scan(spl_thread_cnt_files, & thread_files_count, NULL, spt_mesh[L_CTLFILE]);
	return  thread_files_count;
}
