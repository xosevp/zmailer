/*
 *	Copyright 1988 by Rayan S. Zachariassen, all rights reserved.
 *	This will be free software, but only when it is finished.
 *
 *	Some modifications  by
 *	Matti Aarnio <mea@nic.funet.fi>  (copyright) 1992-2003
 */

/*LINTLIBRARY*/

#include "hostenv.h"

#include <stdio.h>

#include <errno.h>
#include <sys/param.h>
#include <sys/stat.h>
#ifdef HAVE_FCNTL_H
# include <fcntl.h>
#endif
#include <sys/file.h>
#include <sys/socket.h>
#ifdef HAVE_SYS_UN_H
#include <sys/un.h>
#endif

#include "mail.h"
#include "zmsignal.h"

#include "listutils.h"
#include "libc.h"
#include "libsh.h"

/*
 * Standard routines that may be used by any program to submit mail.
 *
 * This file should be part of the standard C library on your system.
 * 
 * The proper use of these routines is as follows:
 *
 *	...
 *      mail_priority = 0;
 *	FILE *mfp = mail_open(type);
 *	if (mfp != NULL) {
 *	... output the mail message to mfp ...
 *	} else
 *		... error handling for not even being able to open the file ...
 *	if (oops)
 *		(void) mail_abort(mfp);
 *	else if (mail_close(mfp) == EOF)
 *		... error handling if something went wrong ...
 *	...
 *
 * Note that the return value from these routines corresponds to the
 * return values of fopen() and fclose() respectively. The routines
 * are single-threaded due to the need to remember a filename.
 *
 * Note also that the mail_alloc() routine is called instead of malloc()
 * directly, allowing applications that make many calls to these routines
 * during the process lifetime to provide an alternate byte allocator
 * that will not cause them to run out of data space.  Similarly, the
 * mail_host() routine is expected to return a unique host identification.
 *
 * Some simple signal handling is advisable too.
 */


/* array of message file name associated with a file descriptor */
static char **mail_file = NULL;
static char **mail_type = NULL;
static int mail_nfiles  = 0;
extern const char *postoffice;	/* may be extern or local */

static int eqrename __((const char *, const char *));
static int
eqrename(from, to)
	const char *from, *to;
{
#ifdef	HAVE_RENAME
	while (rename(from, to) < 0) {
	  int serrno = errno;
	  if (errno == EBUSY || errno == EINTR) {
	    /* Solaris says EBUSY, we clean up.. */
	    while (unlink(to) < 0) {
	      if (errno == EBUSY || errno == EINTR)
		continue; /* Crazy Solaris 2.x (including 2.6!) */
	      /* Actually Solaris reports only EBUSY, but .. */
	      break;
	    }
	    /* Solaris says EBUSY, we retry.. */
	    continue;
	  }
	  errno = serrno;
	  return -1;
	}

#else	/* !HAVE_RENAME */
	
	if ((unlink(to) < 0 && errno != ENOENT) ||
	    (link(from, to) < 0)) {
	  return -1;
	}

	if (unlink(from) < 0) {
	  int serrno = errno;
	  unlink(to);
	  errno = serrno;
	  return -1;
	}
#endif	/* !HAVE_RENAME */

	return 0;
}



/*
  Define sending mail priority.
*/

extern int mail_priority;

/*
 * Makes a temporary file under the postoffice, based on a file name
 * template.  The last '%' character of the file name passed will be
 * overwritten with different suffix characters until the open()
 * succeeds or we have exhausted the search space.  Note: a single
 * process cannot hold more than number-of-suffix-characters message
 * files at once.
 */

FILE *
_mail_fopen(filenamep)
	char **filenamep;
{
	const char *suffix, *post;
	char *path, *cp;
	FILE *fp;
	int fd, eno;

	if (postoffice == NULL &&
	    (postoffice = getzenv("POSTOFFICE")) == NULL)
	  postoffice = POSTOFFICE;

	path = mail_alloc(strlen(postoffice)+strlen(*filenamep)+2);
	sprintf(path, "%s/%s", postoffice, *filenamep);
	for (cp = *filenamep; *cp != '\0' && *cp != '%'; ++cp)
		continue;
	if (*cp == '%') {
		post = cp + 1;
		cp = (cp - *filenamep) + strlen(postoffice) + 1 + path;
	} else
		post = cp = NULL;
	fp = NULL;
	eno = 0;
	for (suffix = SUFFIXCHARS; *suffix != 0; ++suffix) {
		if (cp == NULL)
			sleep(2); /* hope something happens meanwhile */
		else if (*suffix != ' ') {
			*cp = *suffix;
			strcpy(cp+1, post);
		} else
			strcpy(cp, post);
		fd = open(path, O_CREAT|O_EXCL|O_RDWR, 0600);
		if (fd >= 0) {
			fcntl(fd, F_SETFD,
			      fcntl(fd, F_GETFD, 0) | FD_CLOEXEC);
			fp = fdopen(fd, "w+");
			if (fp) {
			  setvbuf(fp, NULL, _IOFBF, 8192);
			  mail_free(*filenamep);
			  *filenamep = path;
			}
			return fp;
		}
		eno = errno;
	}
	mail_free(path);
	errno = eno;
	return fp;
}

/*
 * Link from-file to a file given by the to-file template.
 * The last '%' character of the to-file name passed will be overwritten
 * with different suffix characters until the link() succeeds or we have
 * exhausted the search space.
 */

int
mail_link(from, tonamep)
	const char *from;
	char **tonamep;
{
	char *path, *cp;
	const char *suffix, *post;
	int eno;

	if (postoffice == NULL &&
	    (postoffice = getzenv("POSTOFFICE")) == NULL)
		postoffice = POSTOFFICE;

	path = mail_alloc(strlen(postoffice)+strlen(*tonamep)+2);
	sprintf(path, "%s/%s", postoffice, *tonamep);
	for (cp = *tonamep; *cp != '\0' && *cp != '%'; ++cp)
		continue;
	if (*cp == '%') {
		post = cp + 1;
		cp = (cp - *tonamep) + strlen(postoffice) + 1 + path;
	} else
		post = cp = NULL;
	eno = 0;
	for (suffix = SUFFIXCHARS; *suffix != 0; ++suffix) {
		if (cp == NULL)
			sleep(2); /* hope something happens meanwhile */
		else if (*suffix != ' ') {
			*cp = *suffix;
			strcpy(cp+1, post);
		} else
			strcpy(cp, post);
		if (eqrename(from, path) >= 0) {
			mail_free(*tonamep);
			*tonamep = path;
			return 0;
		}
		eno = errno;
	}
	mail_free(path);
	errno = eno;
	return -1;
}

/*
 * Open a message file of the specified type and initialize generic
 * envelope information (i.e. the file position on return may not be 0).
 */

FILE *
mail_open(type)
	const char *type;
{
	char *scratch;
	const char *cp;
	FILE *fp;
	int eno, fn;
	struct stat stbuf;
	char namebuf[BUFSIZ];
	static const char *host = NULL;
	
	/* Create a file, any file, in the PUBLIC directory */

	if (host == NULL)
		host = mail_host();
	cp = (host == NULL) ? "I" : host ;
	scratch = mail_alloc(strlen(PUBLICDIR)+strlen(cp)+3+1+10);

	sprintf(scratch, "%s/%.19s:%d%%", PUBLICDIR, cp, (int)getpid());

	fp = _mail_fopen(&scratch);
	if (fp == NULL) {
	  eno = errno;
	  fprintf(stderr, "mail_fopen(\"%s\", \"w+\"): errno %d\n",
		  scratch, errno);
	  mail_free(scratch);
	  errno = eno;
	  return NULL;
	}

	/* Determine a unique id associated with the file
	   (inode number) */

	fn = FILENO(fp);
	if (fstat(fn, &stbuf) < 0) {
	  eno = errno;
	  fprintf(stderr, "fstat(\"%s\"): errno %d\n", scratch, errno);
	  mail_free(scratch);
	  errno = eno;
	  return NULL;
	}

	/* Rename the scratch file to the message file name
	   based on the id */

	if (type == NULL)
		type = MSG_RFC822;

#ifdef notype
	type = "";
#endif

	/* Extend when need! */
	
	if (fn >= mail_nfiles) {
	  int nfile = fn+1;
	  if (mail_file == NULL) {
	    mail_file = (char**)mail_alloc((u_int)(sizeof(char*) *
						   nfile));
	    mail_type = (char**)mail_alloc((u_int)(sizeof(char*) *
						   nfile));
	  } else {
	    mail_file = (char**)mail_realloc((char*)mail_file,
					     (sizeof(char*) * nfile));
	    mail_type = (char**)mail_realloc((char*)mail_type,
					     (sizeof(char*) * nfile));
	  }
	  while (mail_nfiles < nfile) {
	    mail_file[mail_nfiles] = NULL;
	    mail_type[mail_nfiles] = NULL;
	    ++mail_nfiles;
	  }
	}

	mail_file[fn] = scratch;
	mail_type[fn] = strdup(type);

	/* Grab preferences from the environment to initialize
	   the envelope */

#ifndef	notype
	if (type != NULL && *type != '\0')
	  fprintf(fp, "type %s\n", type);
#endif
	cp = getenv("FULLNAME");
	if (cp != NULL)
	  fprintf(fp, "fullname %s\n",
		   fullname(cp, namebuf, sizeof namebuf, (char *)NULL));
	cp = getenv("PRETTYLOGIN");
	if (cp != NULL)
	  fprintf(fp, "loginname %s\n", cp);

	/*
	 * If the postoffice lives elsewhere, put our hostname
	 * in the Received-from header, to aid in message tracing.
	 */
#if 0
	host = whathost(scratch);
	if (getzenv("MAILSERVER") != NULL ||
	    (host != NULL && strcmp(host,"localhost") != 0))
#endif
	  if (getmyhostname(namebuf, sizeof namebuf) == 0) {
	    cp = getenv("LOGNAME");
	    if (cp == NULL)
	      cp = getenv("USERNAME");
	    if (cp == NULL)
	      cp = getenv("USER");
	    if (cp == NULL)
	      cp = "\"??\"";
	    fprintf(fp, "rcvdfrom STDIN (%s@%s)\n", cp, namebuf);
	  }
	return fp;
}


/*
 * Return currently open spool file name
 */

char *
mail_fname(fp)
	FILE *fp;
{
	int fd = FILENO(fp);

	if (fd < 0 || fd >= mail_nfiles)
	  return NULL;

	return mail_file[fd];
}


/*
 * Abort the message file composition on the indicated stream.
 */

int
mail_abort(fp)
	FILE *fp;
{
	register char *message;
	int r, fn;

	if (fp == NULL) {
		errno = EBADF;
		return -1;
	}
	fn = FILENO(fp);
	if (fn >= mail_nfiles)
		abort(); /* Usage error -- no such fileno in our use! */
	if (mail_type[ fn ]) mail_free(mail_type[fn]);
	mail_type[ fn ] = NULL;
	message = mail_file[ fn ];
	if (message == NULL) {
		errno = ENOENT;
		return -1;
	}
	fclose(fp);
	mail_file[ fn ] = NULL;
	r = unlink(message);
	mail_free(message);
	return r;
}

/*
 * Close the message file on the indicated stream and submit it to
 * the mailer.
 */

int mail_close(fp)
	FILE *fp;
{
	return _mail_close_(fp, NULL, NULL, NULL);
}


static int routersubdirhash = -1;

static int
_mail_close__(fp,inop, mtimep, mtimensp, async)
	FILE *fp;
	long *inop, *mtimensp;
	time_t *mtimep;
	int async;
{
	char *message, *nmessage, *type, *ftype;
	const char *routerdir;
	const char *inputdirs;
	char *s = NULL;
	struct stat stb;
	int disable_routerdirhash = 0;
	int fn;
	long ino;
	char subdirhash[6];

	if (postoffice == NULL) {
		fprintf(stderr, "mail_close: called out of order!\n");
		errno = EINVAL;
		return -1;
	}
	if (fp == NULL) {
		errno = EBADF;
		return -1;
	}
	fn = FILENO(fp);
	if (fn >= mail_nfiles)
		abort(); /* Usage error -- no such fileno in our use! */
	message = mail_file[fn];
	if (message == NULL) {
		errno = ENOENT;
		return -1;
	}
	ftype = type = mail_type[fn];
	if (type == NULL) {
		type = "";
	}

	mail_type[fn] = NULL;
	mail_file[fn] = NULL;

	if (fstat(fn, &stb)) {
	  /* XXX: error processing */
	}
	ino = stb.st_ino;

	/*
	 * *** NFS users beware ***
	 * the fsync() between fflush() and fclose() may be mandatory
	 * on NFS mounted postoffices if you want to guarantee not losing
	 * data without being told about it.
	 */

	while (fflush(fp) != 0) {
	  if (errno == EINTR || errno == EAGAIN)
	    continue;
	  mail_free(message);
	  if (ftype) mail_free(ftype);
	  errno = EIO;
	  return -1;
	}
#ifdef HAVE_FSYNC
	if (!async) {
	  while (fsync(fn) < 0) {
	    if (errno == EINTR || errno == EAGAIN)
	      continue;
	    if (ftype) mail_free(ftype);
	    mail_free(message);
	    errno = EIO;
	    return -1;
	  }
	}
#endif
	if (fclose(fp) == EOF) {
	  mail_free(message);
	  if (ftype) mail_free(ftype);
	  errno = EIO;
	  return -1;
	}

	inputdirs = getzenv("INPUTDIRS");

	routerdir = NULL;
	nmessage  = NULL;
	s         = NULL;

	if (inputdirs) {
	  int i = mail_priority;
	  const char *rd = inputdirs;
	  const char *ord = NULL;
#ifdef HAVE_ALLOCA
	  nmessage = alloca(strlen(postoffice)+strlen(inputdirs)+3+
			    9+4+strlen(type));
#else
	  nmessage = mail_realloc(nmessage,
				  strlen(postoffice)+strlen(inputdirs)+3+
				  9+4+strlen(type));
#endif
	  /* There are some defined!   A ":" separated list of strings */

	  /* mail_priority == 1 pics first, 2 pics second, ..
	     if segments run out, last one is kept at  rd     */

	  s = strchr(rd, ':');

	  while (i-- && (s = strchr(rd,':'))) {
	    *s = 0;
	    sprintf(nmessage, "%s/%s", postoffice, rd);
	    *s = ':';
	    if ((stat(nmessage,&stb) < 0) || !S_ISDIR(stb.st_mode)) {
	      rd = s+1;
	      continue;	/* Not ok -- not a dir, for example */
	    }
	    ord = rd;
	    rd = s+1;
	  }
	  
	  /* Here we are when there is only one entry in the inputdirs:*/
	  if (ord == NULL && *rd != 0) {
	    if (s) *s = 0;
	    sprintf(nmessage, "%s/%s", postoffice, rd);
	    if (s) *s = ':';
	    /* Is it a valid directory ? */
	    if ((stat(nmessage,&stb) == 0) && S_ISDIR(stb.st_mode))
	      ord = rd; /* IT IS ! */
	  }
	  routerdir = ord;
	  if (ord) disable_routerdirhash = 1;
	}


	if (!routerdir && !mail_priority)
	  routerdir = ROUTERDIR;

	if (mail_priority && !routerdir) {
	  /* We are asked to place the mail somewhere else */
	  const char *routerdirs = getzenv("ROUTERDIRS");
	  routerdir = ROUTERDIR;
	  if (routerdirs) {
	    int i = mail_priority;
	    const char *rd = routerdirs;
	    const char *ord = routerdir;
#ifdef HAVE_ALLOCA
	    nmessage = alloca(strlen(postoffice)+strlen(routerdirs)+
			      3+9+4+strlen(type));
#else
	    nmessage = mail_realloc(nmessage,
				    strlen(postoffice)+strlen(routerdirs)+
				    3+9+4+strlen(type));
#endif
	    /* There are some defined!
	       A ":" separated list of strings */

	    /* mail_priority == 1 pics first, 2 pics second, ..
	       if segments run out, last one is kept at  rd     */

	    while (i-- && (s = strchr(rd,':'))) {
	      *s = 0;
	      sprintf(nmessage, "%s/%s", postoffice, rd);
	      *s = ':';
	      if ((stat(nmessage,&stb) < 0) || !S_ISDIR(stb.st_mode)) {
		rd = s+1;
		continue;	/* Not ok -- not a dir, for example */
	      }
	      ord = rd;
	      rd = s+1;
	    }

	    /* Here we are when there is only one entry in
	       the routerdirs: */
	    if (s == NULL && i > 0 && *rd != 0) {
	      if (s) *s = 0;
	      sprintf(nmessage, "%s/%s", postoffice, rd);
	      if (s) *s = ':';
	      /* Is it a valid directory ? */
	      if ((stat(nmessage,&stb) == 0) && S_ISDIR(stb.st_mode))
		ord = rd; /* IT IS ! */
	    }
	    routerdir = ord;
	  }
	}

	if (routersubdirhash < 0) {
	  const char *ss;
	  if (disable_routerdirhash)
	    ss = getzenv("INPUTDIRHASH");
	  else
	    ss = getzenv("ROUTERDIRHASH");

	  if (ss && *ss == '1')
	    routersubdirhash = 1;
	  else
	    routersubdirhash = 0;
	}

	if (routersubdirhash > 0) {
	  sprintf(subdirhash, "%c/", (int)('A' + (ino % 26)));
	} else
	  *subdirhash = 0;


	/* Assert postoffice != NULL */
	if (nmessage == NULL) {
#ifdef HAVE_ALLOCA
	  nmessage = alloca(strlen(postoffice)+strlen(routerdir)+
			    9+4+2+1+strlen(type));
#else
	  nmessage = mail_realloc(nmessage,
				  strlen(postoffice)+strlen(routerdir)+
				  9+4+2+1+strlen(type));
#endif
	  sprintf(nmessage, "%s/%s/%s%ld%s", postoffice, routerdir,
		  subdirhash, ino ,type);
	} else {
	  s = strchr(routerdir,':');
	  if (s) *s = 0;
	  sprintf(nmessage, "%s/%s/%s%ld%s", postoffice, routerdir,
		  subdirhash, ino, type);
	  if (s) *s = ':';
	}

	/* For performance reasons we optimize heavily.. */

	if (eqrename(message,nmessage) != 0) {
	  int eno = errno;
	  fprintf(stderr, "link(\"%s\", \"%s\"): errno %d\n",
		  message, nmessage, errno);
	  if (ftype) mail_free(ftype);
	  mail_free(message);
	  mail_free(nmessage);
	  errno = eno;
	  return -1;
	}

	stat(nmessage, &stb);

#ifdef AF_UNIX
	do {

	  const char *routernotify;
	  char buf[1000];
	  int notifysocket;
	  struct sockaddr_un sad;
#ifndef MSG_NOSIGNAL
	  RETSIGTYPE (*oldsig)__((int));
#endif

	  if (disable_routerdirhash)
	    routernotify = getzenv("INPUTNOTIFY");
	  else
	    routernotify = getzenv("ROUTERNOTIFY");

	  if (!routernotify) break;

	  memset(&sad, 0, sizeof(sad));
	  sad.sun_family = AF_UNIX;
	  strncpy(sad.sun_path, routernotify, sizeof(sad.sun_path));
	  sad.sun_path[ sizeof(sad.sun_path)-1 ] = 0;

	  notifysocket = socket(PF_UNIX, SOCK_DGRAM, 0);
	  if (notifysocket < 0) {
	    perror("notifysocket: socket(PF_UNIX)");
	    break;
	  }

	  fcntl(notifysocket, F_SETFL, O_NONBLOCK);

	  s = strchr(routerdir,':');
	  if (s) *s = 0;

	  sprintf(buf, "NEW %s %s%ld%s",
		  routerdir, subdirhash, ino, type);

	  if (s) *s = ':';

#ifndef MSG_NOSIGNAL
	  SIGNAL_HANDLESAVE(SIGPIPE, SIG_IGN, oldsig);
#endif

	  sendto(notifysocket, buf, strlen(buf),
#ifdef MSG_NOSIGNAL
		 MSG_NOSIGNAL|
#endif
#ifdef MSG_DONTWAIT
		 MSG_DONTWAIT
#endif
		 ,
		 (struct sockaddr *)&sad, sizeof(sad));

	  close(notifysocket);
#ifndef MSG_NOSIGNAL
	  SIGNAL_HANDLE(SIGPIPE, oldsig);
#endif

	} while(0);
#endif /* AF_UNIX */

#ifndef HAVE_ALLOCA
	mail_free(nmessage);
#endif
	mail_free(message);
	if (ftype) mail_free(ftype);

	if (inop != NULL)
	  *inop   = (long) stb.st_ino;
	if (mtimep != NULL)
	  *mtimep = (time_t) stb.st_mtime;
	if (mtimensp != NULL) {
#ifdef HAVE_STRUCT_STAT_ST_ATIM_TV_NSEC
	  * mtimensp = stb.st_mtim.tv_nsec;
#else
#ifdef HAVE_STRUCT_STAT_ST_ATIM___TV_NSEC
	  * mtimensp = stb.st_mtim.__tv_nsec;
#else
#ifdef HAVE_STRUCT_STAT_ST_ATIMENSEC
	  * mtimensp = stb.st_mtimensec;
#else
	  * mtimensp = 0;
#endif
#endif
#endif
	}


	return 0;
}


int
_mail_close_(fp,inop, mtimep, mtimensp)
	FILE *fp;
	long *inop, *mtimensp;
	time_t *mtimep;
{
	return _mail_close__(fp, inop, mtimep, mtimensp, 0);
}

int
_mail_close_async(fp,inop, mtimep, mtimensp, async)
	FILE *fp;
	long *inop, *mtimensp;
	time_t *mtimep;
	int async;
{
	return _mail_close__(fp, inop, mtimep, mtimensp, async);
}



/*
 * Close the message file on the indicated stream, and submit
 * it to alternate directory. (For smtpserver->scheduler messages,
 * for example.)
 */

static int
mail_close_alternate_(fp,where,suffix,async)
	FILE *fp;
	const char *where, *suffix;
	int async;
{
	char *message, *nmessage, *msgbase;
	char *type, *ftype;
	struct stat stbuf;
	int fn;

	if (postoffice == NULL) {
	  fprintf(stderr,
		  "mail_close_alternate: called out of order!\n");
	  errno = EINVAL;
	  return -2;
	}
	if (fp == NULL) {
	  errno = EBADF;
	  return -2;
	}
	fn = FILENO(fp);
	fstat(fn, &stbuf);
	if (fn >= mail_nfiles)
	  abort(); /* Usage error -- no such fileno in our use! */

	message = mail_file[fn];
	if (message == NULL) {
		errno = ENOENT;
		return -1;
	}
	type = ftype = mail_type[fn];
	if (type == NULL)
	  type = "";

	mail_file[fn] = NULL;
	mail_type[fn] = NULL;

	/*
	 * *** NFS users beware ***
	 * the fsync() between fflush() and fclose() may be mandatory
	 * on NFS mounted postoffices if you want to guarantee not losing
	 * data without being told about it.
	 */


	while (fflush(fp) != 0) {
	  if (errno == EINTR || errno == EAGAIN)
	    continue;
	  mail_free(message);
	  if (ftype) mail_free(ftype);
	  errno = EIO;
	  return -1;
	}
#ifdef HAVE_FSYNC
	while (fsync(fn) < 0) {
	  if (errno == EINTR || errno == EAGAIN)
	    continue;
	  if (ftype) mail_free(ftype);
	  mail_free(message);
	  errno = EIO;
	  return -1;
	}
#endif
	if (fclose(fp) == EOF) {
	  mail_free(message);
	  if (ftype) mail_free(ftype);
	  errno = EIO;
	  return -1;
	}

	/* Find the base name (we know format is PUBLICDIR/basename) */
	msgbase = strrchr(message, '/');
	if (msgbase == NULL)
		msgbase = message;
	else
		++msgbase;

	/* Assert postoffice != NULL */

	nmessage = mail_alloc(strlen(postoffice)+1+strlen(where)+1+
			      20+strlen(suffix)+1+strlen(type));

	sprintf(nmessage, "%s/%s/%ld%s%s",
		postoffice, where, (long)stbuf.st_ino, suffix, type);

	if (eqrename(message,nmessage) != 0) {
	  int eno = errno;
	  fprintf(stderr, "eqrename(\"%s\", \"%s\"): errno %d\n",
		  message, nmessage, errno);
	  mail_free(message);
	  mail_free(nmessage);
	  if (ftype) mail_free(ftype);
	  errno = eno;
	  return -1;
	}

	mail_free(message);
	mail_free(nmessage);
	if (ftype) mail_free(ftype);
	return 0;
}

int
mail_close_alternate(fp,where,suffix)
	FILE *fp;
	const char *where, *suffix;
{
	return mail_close_alternate_(fp, where, suffix, 0);
}

int
mail_close_alternate_async(fp,where,suffix,async)
	FILE *fp;
	const char *where, *suffix;
	int async;
{
	return mail_close_alternate_(fp, where, suffix, async);
}
