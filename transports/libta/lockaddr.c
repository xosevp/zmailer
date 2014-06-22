/*
 *	Copyright 1988 by Rayan S. Zachariassen, all rights reserved.
 *	This will be free software, but only when it is finished.
 *
 *  mmap() using region mapping -- gives efficiency at message
 *  lock accesses
 *
 *  FCNTL-style locking by Matti Aarnio <mea@nic.funet.fi>
 *  Theory:  On system where it works, it makes LESS IO
 */

/*
 * Common routine to fiddle control file tag characters.
 */

#include "hostenv.h"
#include <stdio.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/file.h>
#include "mail.h"
#include "ta.h"
#include "libc.h"

#undef HAVE_FCNTL  /* No, sorry, not really defined locking method! */

#ifndef	SEEK_SET
#define	SEEK_SET  0
#endif	/* SEEK_SET */

static const char *ta_lockmode = NULL;

int
lockaddr(fd, map, offset, was, new, file, host, mypid)
	int	fd;
	char	*map;
	int	offset;
	int	was;
	int	new;
	const char *file, *host;
	const int mypid;
{
	char	lockbuf[16]; /* FIXME: MAGIC SIZE KNOWLEDGE! */
	int	newlock = 0;
	int	do_mmap = 0;

	if (!ta_lockmode) {
	  ta_lockmode = getzenv("TALOCKMODE");
#if defined(HAVE_MMAP)
	  if (!ta_lockmode && ta_use_mmap > 0) {
	    ta_lockmode = "M"; /* MMAP */
	  } else {
#ifdef HAVE_FCNTL
	    if (!ta_lockmode) ta_lockmode = "F"; /* FCNTL */
#else
	    if (!ta_lockmode) ta_lockmode = "W"; /* WRITE */
#endif
	  }
	  do_mmap = (*ta_lockmode == 'M'  && map);
#else
#ifdef HAVE_FCNTL
	  if (!ta_lockmode) ta_lockmode = "F"; /* FCNTL */
#else
	  if (!ta_lockmode) ta_lockmode = "W"; /* WRITE */
#endif
#endif
	}
#ifdef HAVE_FCNTL
	if (*ta_lockmode == 'F') {
	  struct flock fl;
	  int rc = 0;

	  fl.l_type   = F_WRLCK;
	  fl.l_start  = offset;
	  fl.l_whence = SEEK_SET;
	  fl.l_len    = 10; /* fixed.. */

	  if (new == _CFTAG_LOCK || new == _CFTAG_DEFER) {
	    rc = fcntl(fd,F_GETLK,&fl);
	    if (rc == -1) {
	      warning("lockaddr: fcntl() lock error");
	      return 0;
	    }
	  }
	  lockbuf[1] = ' ';
	  if (was == _CFTAG_NORMAL) {
	    if (fl.l_type == F_UNLCK)
	      lockbuf[0] = was;
	    else
	      lockbuf[0] = _CFTAG_LOCK;
	  } else if (was == _CFTAG_LOCK) {
	    if (fl.l_type == F_UNLCK)
	      lockbuf[0] = new;
	    else
	      lockbuf[0] = was; /* XXX: Hmm... */
	  }
	}
#endif
	if (do_mmap) {
	  /* MMAP()ed block helps.. */
	  memcpy(lockbuf,map+offset,sizeof(lockbuf));
	} else {
	  if (lseek(fd, offset, SEEK_SET) < 0L) {
	    warning("lockaddr: lseek() failure");
	    return 0;
	  }
	  if (read(fd, lockbuf, sizeof(lockbuf)) != sizeof(lockbuf)) {
	    warning("lockaddr: read() failure");
	    return 0;
	  }
	}
	newlock = ((lockbuf[1] == ' ') ||
		   (lockbuf[1] >= '0' && lockbuf[1] <= '9'));
	if (lockbuf[0] == was) {
	  if (!map && lseek(fd, offset, SEEK_SET) < 0L) {
	    warning("lockaddr: lseek() failure 2");
	    return 0;
	  }
	  lockbuf[0] = new;
	  if (newlock) {
	    if (new == _CFTAG_LOCK) {	/* '~' */
	      /* Mark the lock with client process-id */
	      sprintf(lockbuf+1, "%*d", _CFTAG_RCPTPIDSIZE, mypid);
	      if (do_mmap)
		memcpy(map+offset, lockbuf, _CFTAG_RCPTPIDSIZE+1);
	      else if (write(fd,lockbuf,
			     _CFTAG_RCPTPIDSIZE+1) != _CFTAG_RCPTPIDSIZE+1)
		return 0;
	    } else if (new == _CFTAG_DEFER) { /* == _CFTAG_NORMAL == ' ' */
#ifdef HAVE_FCNTL
	      /* Using FCNTL region locking */
#else
	      /* Clear the lock location */
	      memset(lockbuf+1, ' ', _CFTAG_RCPTPIDSIZE);
	      if (do_mmap)
		memcpy(map+offset, lockbuf, _CFTAG_RCPTPIDSIZE+1);
	      else if (write(fd,lockbuf,
			     _CFTAG_RCPTPIDSIZE+1) != _CFTAG_RCPTPIDSIZE+1)
		return 0;
#endif
	    } else {
	      /* Clear the lock location */
	      if (!(was == _CFTAG_NORMAL && new == _CFTAG_OK))
		/* ... but not when the scheduler calls this to mark off
		   the diagnostics lines. */
		memset(lockbuf+1, ' ', _CFTAG_RCPTPIDSIZE);

	      if (do_mmap)
		memcpy(map+offset, lockbuf, _CFTAG_RCPTPIDSIZE+1);
	      if ((!do_mmap) ||
		  (do_mmap && (new == _CFTAG_OK || new == _CFTAG_NOTOK))) {
		if (write(fd,lockbuf,
			  _CFTAG_RCPTPIDSIZE+1) != _CFTAG_RCPTPIDSIZE+1)
		  return 0;
	      }
	    }
	  }
	  return 1;
	}
	if (host == NULL) host = "-";
	warning("lockaddr: file '%s' host '%s' expected '%c' found '%c'\n", file, host, was, new);
	return 0;
}
