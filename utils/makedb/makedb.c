/* Copyright 1993-2006 - Matti Aarnio

   The way the Zmailer uses DBM entries is by using strings with
   their terminating NULL as keys, and as data..  Thus the length
   is strlen(string)+1, not strlen(string) !
 */

/*
 * WARNING: Policy data parsing does use unchecked buffers!
 */

#define NO_Z_IO_H
#include "../lib/linebuffer.c"
#include <stdio.h>
#include <ctype.h>
#include <sys/types.h>
#include <fcntl.h>
#ifdef HAVE_NDBM
#define datum Ndatum
#include <ndbm.h>
#undef datum
#endif
#ifdef HAVE_GDBM
#define datum Gdatum
#include <gdbm.h>
#undef datum
#endif

#include "sleepycatdb.h"

#define _POLICYTEST_INTERNAL_
#include "policy.h"

#define PROG "makedb"

#include <errno.h>
extern int errno;	/* Not all systems declare it in <errno.h>, sigh ... */

extern int optind;
int  store_errors = 0;
char *progname    = NULL;
int   D_alloc     = 0;
int   verbose     = 0;
int   append_mode = 0;
int   lc_key	  = 0;
int   uc_key      = 0;
int   silent      = 0;
int   aliasinput  = 0;
int   policyinput = 0;


/* extern char *strchr(); */

extern void  create_dbase   __((FILE *, void *, int));
extern char *skip821address __((char *));
extern void  usage          __((const char *, const char *, int));

void usage(prog, errs, err)
const char *prog, *errs;
int err;
{
	fprintf(stderr, "Usage: %s [-l|-u]] [-A][-a|-p][-s] dbtype database.name [infilename|-]\n", prog);
	fprintf(stderr, "  where supported dbtypes are:");
#ifdef HAVE_NDBM
	fprintf(stderr, " ndbm");
#endif
#ifdef HAVE_GDBM
	fprintf(stderr, " gdbm");
#endif
#ifdef HAVE_DB
	fprintf(stderr, " btree bhash");
#endif
	fprintf(stderr, "\n");
	fprintf(stderr, " Error now: %s", errs);
	if (err != 0) {
	  fprintf(stderr, ", errno=%d (%s)", err, strerror(err));
	  fprintf(stderr, "\n");
	  exit(1);
	}
	fprintf(stderr, "\n\n  If no infilename is defined, database.name is assumed.\n");
#ifdef HAVE_NDBM
	fprintf(stderr, "  (NDBM appends  .pag, and .dir  into actual db file names..)\n");
#endif
#ifdef HAVE_GDBM
	fprintf(stderr, "  (GDBM appends .gdbm, to the actual db file name..)\n");
#endif
#ifdef HAVE_DB
	fprintf(stderr, "  (BTREE appends .db, to the actual db file name..)\n");
	fprintf(stderr, "  (BHASH appends .pag, and .dir into actual db file names..)\n");
#if defined(HAVE_DB2) || defined(HAVE_DB3) || defined(HAVE_DB4)
	fprintf(stderr, "    (Version: %s)\n", db_version(NULL,NULL,NULL));
#else
	fprintf(stderr, "  (Version 1.x ?)\n");
#endif
#endif
	fprintf(stderr, "\n");

	fprintf(stderr,
"  The '-a' option is for parsing input that comes in\n\
  'aliases' format:  'key: data,in,long,line,'\n\
                     '  with,indented,extended,lines'\n\
  The '-p' option is for parsing smtpserver policy database.\n\
  The '-A' option APPENDS new data to existing keyed data.\n\
  The '-l' and '-u' will lower-/uppercasify key string before\n\
    storing it into the database.  This does not apply to '-p'.\n\
  The '-s' option orders 'silent running' -- report only errors.\n");

	exit(64);
}


/* KK() and KA() macroes are at "policy.h" */

static char *showkey __((const char *key));
static char *showkey(key)
const char *key;
{
    static char buf[256];

    if (key[1] != P_K_IPv4 && key[1] != P_K_IPv6) {
	if (strlen(key+2) > (sizeof(buf) - 200))
	    sprintf(buf,"%d/%s/'%s'", key[0], KK(key[1]), "<too long name>");
	else
	    sprintf(buf,"%d/%s/'%s'", key[0], KK(key[1]), key+2);
    } else
      if (key[1] == P_K_IPv4)
	sprintf(buf,"%d/%s/%u.%u.%u.%u/%d",
		key[0], KK(key[1]),
		key[2] & 0xff, key[3] & 0xff, key[4] & 0xff, key[5] & 0xff,
		key[6] & 0xff);
      else
	sprintf(buf,"%d/%s/%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x/%d",
		key[0], KK(key[1]),
		key[2] & 0xff, key[3] & 0xff, key[4] & 0xff, key[5] & 0xff,
		key[6] & 0xff, key[7] & 0xff, key[8] & 0xff, key[9] & 0xff,
		key[10] & 0xff, key[11] & 0xff, key[12] & 0xff, key[13] & 0xff,
		key[14] & 0xff, key[15] & 0xff, key[16] & 0xff, key[17] & 0xff,
		key[18] & 0xff);
    return buf;
}


static int store_db __((void *, const int, const int, const int, const void *, const int, const void *, const int));

static int store_db(dbf, typ, overwritemode, linenum, t, tlen, s, slen)
     void *dbf;
     const int typ, linenum;
     const void *s, *t;
     const int slen, tlen, overwritemode;
{
#ifdef HAVE_NDBM
	DBM *ndbmfile = dbf;
#endif
#ifdef HAVE_GDBM
	GDBM_FILE gdbmfile = dbf;
#endif
#ifdef HAVE_DB
	DB *dbfile = dbf;
#endif
	int rc = -2;

	if (verbose) {
	  if (policyinput) {
	    const char *k = (const char *)t;
	    fprintf(stderr, "Storing key='%s' data=...\n", showkey(k));
	  } else
	    fprintf(stderr, "Storing key='%s' data='%s'\n",
		    (const char*)t, (const char *)s);
	}


	switch (typ) {
#ifdef HAVE_NDBM
	case 1:
	  {
	    Ndatum Ndat, Nkey;
	    Nkey.dptr = (void*)t;
	    Nkey.dsize = tlen;
	    Ndat.dptr = (void*)s;
	    Ndat.dsize = slen;
	    rc = dbm_store(ndbmfile, Nkey, Ndat,
			   overwritemode ? DBM_REPLACE : DBM_INSERT);

	    if (rc < 0 && errno == ENOSPC) {
	      fprintf(stderr,"NDBM does not allow KEY.LEN + DATA.LEN to exceed 1024 bytes!  linenro=%d\n",linenum);
	    }
	  }
	  break;
#endif
#ifdef HAVE_GDBM
	case 2:
	  {
	    Gdatum Gdat, Gkey;
	    Gkey.dptr = (void*)t;
	    Gkey.dsize = tlen;
	    Gdat.dptr = (void*)s;
	    Gdat.dsize = slen;
	    rc = gdbm_store(gdbmfile, Gkey, Gdat,
			    overwritemode ? GDBM_REPLACE : GDBM_INSERT);
	  }
	  break;
#endif
#ifdef HAVE_DB
	case 3: case 4:
	  {
	    DBT Bkey, Bdat;

	    memset(&Bkey,0,sizeof(Bkey));
	    memset(&Bdat,0,sizeof(Bdat));

	    Bkey.data = (void*)t;
	    Bkey.size = tlen;

	    Bdat.data = (void*)s;
	    Bdat.size = slen;

#ifdef DB_INIT_TXN
	    rc = (dbfile->put) (dbfile, NULL, &Bkey, &Bdat,
				overwritemode ? 0: DB_NOOVERWRITE);

	    /* emulate BSD DB 1.85 return values */
	    rc = -rc;

#else
	    rc = (dbfile->put) (dbfile, &Bkey, &Bdat,
				overwritemode ? 0: R_NOOVERWRITE);
#endif
	  }
	  break;
#endif
	} /* end of switch(typ) ... */


	if (rc > 0 && append_mode == 0)
	  return rc; /* Duh! Duplicate, and no append_mode :-( */

	if (rc > 0 && overwritemode == 0) {
	  /* we shall try append, at first we have to get the old
	     data, and then append to it... */

	  void *dataptr = NULL;
	  int   datalen = 0;
	  char *newptr = NULL;
	  int   newlen = 0;

	  switch (typ) {

#ifdef HAVE_NDBM
	  case 1:
	    {
	      Ndatum Ndat, Nkey;
	      Nkey.dptr = (void*)t;
	      Nkey.dsize = tlen;
	      Ndat = dbm_fetch(ndbmfile, Nkey);
	      dataptr = Ndat.dptr;
	      datalen = Ndat.dsize;
	    }
	    break;
#endif
#ifdef HAVE_GDBM
	  case 2:
	    {
	      Gdatum Gdat, Gkey;
	      Gkey.dptr = (void*)t;
	      Gkey.dsize = tlen;
	      Gdat = gdbm_fetch(gdbmfile, Gkey);
	      dataptr = Gdat.dptr; /* Must free() this */
	      datalen = Gdat.dsize;
	    }
	    break;
#endif
#ifdef HAVE_DB
	  case 3: case 4:
	    {
	      DBT Bkey, Bdat;

	      memset(&Bkey,0,sizeof(Bkey));
	      memset(&Bdat,0,sizeof(Bdat));

	      Bkey.data = (void*)t;
	      Bkey.size = tlen;
#ifdef DB_INIT_TXN
	      rc = (dbfile->get) (dbfile, NULL, &Bkey, &Bdat, 0);
#else
	      rc = (dbfile->get) (dbfile, &Bkey, &Bdat, 0);
#endif
	      if (rc != 0)
		memset(&Bdat, 0, sizeof(Bdat));
	      dataptr = Bdat.data;
	      datalen = Bdat.size;
	    }
	    break;
#endif
	  } /* end of .. switch(typ) ... */

	  /* Ok, now we have  dataptr  and  datalen -- we should have
	     non-NULL dataptr.  We need to build a new block with
	     combined data */

	  if (dataptr == NULL)
	    return -1; /* Duh !? */

	  newlen = datalen + slen;
	  newptr = emalloc(newlen + 4);

	  if (append_mode > 0) { /* Ordinary alias append */
	    --datalen;
	    memcpy(newptr, dataptr, datalen);
	    memcpy(newptr + datalen, ",\n\t", 3);
	    memcpy(newptr + datalen + 3, s, slen);
	    newlen = datalen + slen + 3;
	  } else { /* append_mode < 0; PolicyDataset append; binary stuff */
	    memcpy(newptr, dataptr, datalen);
	    memcpy(newptr + datalen, s, slen);
	  }
	  if (typ == 2)
	    free(dataptr); /* GDBM fetched datablock must be freed */

	  rc = store_db(dbf, typ, 1, linenum, t, tlen, newptr, newlen);

	  free(newptr);    /* Our temporary datablock must be freed */
	  return rc;
	}

	if (rc < 0)
		store_errors = 1;
	return rc;
}

extern int parsepolicykey __((void *, char *));
extern int parseattributepair __((void *, char *, char *));

/* Scan over quoted string with embedded white spaces, or
   in case the object does not start with a double quote,
   just all non-white-space chars.   */


static char *tokskip __((char *, char **));
static char *
tokskip(s, sout)
char *s;
char **sout;
{
	char *start;

	while (*s == ' ' || *s == '\t')
	  ++s;
	*sout = s;

	if (*s == '\0')
	  return NULL;

	if (*s == '"') {
	  ++s;
	  start = s;
	  /* Scan thru the quoted string:
	      "message text right here"  */
	  while (*s != '\0') {
	    if (*s == '"') {
	      /* Ending double-quote */
	      *s = '\0';
	      ++s;
	      break;
	    }
	    ++s;
	  }
	} else {
	  start = s;
	  /* Scan over non-white-space chars */
	  while (*s != '\0' && *s != ' ' && *s != '\t')
	    ++s;
	  if (*s != '\0')
	    *(s++) = '\0';
	}
	*sout = s;
	return start;
}

int create_policy_dbase(infile, dbf, typ)
FILE *infile;
void *dbf;
const int typ;
{
	char policykeybuf[256];	/* Plenty enough ? */
	char policydata[16*1024];
	char *s, *t, *str1, *str2;
	int rc, tlen, slen, llen;
	int errflag = 0;

	int policydatalen = 0;
	int linenum = 0;

	/* Turn the append_mode into negative value -- this tells
	   store_db() to work differently from alias append */
	append_mode = -append_mode;

	while ((llen = zgetline(infile)) != 0) {
		++linenum;
		policydatalen = 0;
		if (zlinebuf[llen-1] != '\n') {
			/* Eh ? No line ending newline ?
			   Ah well, there is always at least one byte
			   of space after the read block. */
			++llen;
			fprintf(stderr, "input line of len %d lacking trailing newline, corrupted file ?\n", llen-1);
			errflag = 1;
		}
		zlinebuf[llen-1] = '\0';

		if (*zlinebuf == '#')
			continue;	/* Comment! */

		if (*zlinebuf == ' ' || *zlinebuf == '\t')
			continue;	/* Starts with a white-space! */

		/* Scan first white-space separated token,
		   point its start with t! */

		t = zlinebuf;
		while (*t == '\t' || *t == ' ')
			++t;

		if (*t == 0)
			continue;		/* Blank line! */
		if (*t == '#')
			continue;		/* Comment.. */
	
		s = t;
		/* scan over first word */
		while (*s && *s != '\t' && *s != ' ')
			++s;
		/* Stopped without line-end NIL ?  Trunc, and advance! */
		if (*s)
			*s++ = 0;

		strlower(t); /* Lowercasify the key */

		rc = parsepolicykey((void *) policykeybuf, t);
		if (rc != 0) {
			/* XX: rc != 0  ==> error */
			fprintf(stderr,
				"Error: line %d: bad policykey, rc = %d\n",
				linenum, rc);
			errflag = 1;
			continue;
		}
		/* Skip LWSP */
		/*      while (*s == ' ' || *s == '\t') ++s;
		 */


		/* Collect attribute pairs */
		str1 = tokskip(s, &s);

		if (!str1 || *str1 == '#')
		  continue; /* Data begins a within line comment, or
			     is completely void.. */

		if (str1 == NULL) {
			fprintf(stderr,
				"Error: No attribute pair on line %d.\n",
				linenum);
			errflag = 1;
			continue;
		} else {
			int err = 0;
			while (1) {
				str2 = tokskip(s, &s);
				if (str2 == NULL) {
					fprintf(stderr,
						"Error: Invalid attribute pair on line %d; aname='%s', value missing.\n",
						linenum, str1);
					errflag = 1;
					err = 1;
					break;
				}
				rc = parseattributepair((void *) &policydata[policydatalen],
							str1, str2);
				if (rc != 0) {
					fprintf(stderr,
						"Error: Invalid attribute pair (\"%s %s\")  on line %d.\n",
						str1, str2, linenum);
					errflag = 1;
					err = 1;
					break;
				}
				policydatalen += policydata[policydatalen] & 0xFF;

				str1 = tokskip(s, &s);
				if (str1 == NULL)
					break;
			}
			if (err)
				continue;
		}

		t = (void *) &policykeybuf[0];
		tlen = (policykeybuf[0] & 0xFF);

		s = (void *) &policydata[0];
		slen = policydatalen;

		rc = store_db(dbf, typ, 0, linenum,
			      t, tlen, s, slen);
		if (rc > 0) {
			char *s;
			fprintf(stderr, "WARNING: Duplicate key at line %d: ",
				linenum);

			s = showkey(policykeybuf);

			fprintf(stderr, "%s\n", s);
		}
	}
	return errflag;
}
    

char *
skipaliastoken(s)
  char *s;
{
  char quote = 0;
  char c;
  while ((c = *s)) {
    if (c == '\\') {
      ++s;
      if (*s == 0)
	break;
    }
    if (c == quote) /* 'c' is non-zero here */
      quote = 0;
    else if (c == '"')
      quote = '"';
    else if (!quote && (c == ' ' || c == '\t' || c == ':'))
      break;
    ++s;
  }

  /* Scan possible white space in between alias token,
     and the colon after it; Zero it while doing this */
  while (*s == '\t' || *s == ' ') {
    *s++ = '\0';
  }

  /* Must have colon, if we have it, we zero it, and return
     pointer to after it. */
  if (*s == ':') {
    *s++ = '\0';
    return s;
  }

  /* Didn't have colon, error! */
  return NULL;
}


int create_aliases_dbase(infile, dbf, typ)
FILE *infile;
void *dbf;
const int typ;
{
	int tlen, slen, llen;
	char *s, *t;
	char *t0 = NULL, *s0 = NULL;
	int  linenum = 0;
	int  errflag = 0;
	int  longest = 0;
	int  count   = 0;
	long totsize = 0;

	while ((llen = zgetline(infile)) != 0) {
		++linenum;
		if (zlinebuf[llen-1] != '\n') {
			/* Eh ? No line ending newline ?
			   Ah well, there is always at least one byte
			   of space after the read block. */
			++llen;
			fprintf(stderr, "input line lacking trailing newline, corrupted file ?\n");
			fprintf(stderr, " len=%d, zlinebuf='%s'\n", llen, zlinebuf);
		}
		zlinebuf[llen-1] = '\0';

		if (verbose)
		  fprintf(stderr,"aliases parser: zgetline() llen=%d, str='%.*s'\n",
			  llen, llen, zlinebuf);

		if (*zlinebuf == '#') {
			/* Comment! */
		store_and_continue:
			if (t0 != NULL) {
				tlen = strlen(t0) + 1;
				slen = strlen(s0) + 1;

				++count;
				totsize += slen;
				if (longest < slen)
				  longest = slen;

				if (uc_key)
				  strupper(t0); /* Uppercasify the key */
				if (lc_key)
				  strlower(t0); /* Lowercasify the key */

				if (store_db(dbf, typ, 0, linenum,
					     t0, tlen, s0, slen) < 0)
					break;
				if (t0) free(t0);  t0 = NULL;
				if (s0) free(s0);  s0 = NULL;
			}
			continue;
		}

		t = zlinebuf;
		/* Key starts at line start, continuation lines start
		   with white-space */

		if (*t == 0)
			goto store_and_continue;	/* Blank line! */

		if (t0 != NULL && (*t == '\t' || *t == ' ')) {
			/* Continuation line */
			while (*t == '\t' || *t == ' ') ++t;
			slen = strlen(s0);
			tlen = strlen(t);
			for (llen = slen; llen > 0; --llen) {
			  /* Chop trailing white-space, if any */
			  if (s0[llen-1] == ' ' || s0[llen-1] == '\t') {
			    s0[llen-1] = '\0';
			  } else
			    break;
			}
			slen = llen; /* Shortened, possibly.. */
			if (s0[llen-1] != ',') {
			  fprintf(stderr, "Line %d: Continuation line on alias without preceeding line ending with comma (',')\n", linenum);
			  errflag = 1;
			  continue;
			}
			s0   = erealloc(s0, slen + tlen + 1);
			memcpy(s0 + slen, t, tlen + 1); /* end NIL included */
			continue;
		}
		if (*t == '\t' || *t == ' ') {
			/* Continuation line without previous key line */
			fprintf(stderr,"Line %d: Continuation line without initial keying line\n", linenum);
			errflag = 1;
			continue;
		}

		/* Ok, we MAY have proper line here.
		   If we now have saved t0/s0, we store them here */
		if (t0 != NULL) {
			tlen = strlen(t0) + 1;
			slen = strlen(s0) + 1;

			++count;
			totsize += slen;
			if (longest < slen)
			  longest = slen;

			if (uc_key)
			  strupper(t0); /* Uppercasify the key */
			if (lc_key)
			  strlower(t0); /* Lowercasify the key */

			if (store_db(dbf, typ, 0, linenum,
				     t0, tlen, s0, slen) < 0)
				break;
			if (t0) free(t0);  t0 = NULL;
			if (s0) free(s0);  s0 = NULL;
		}

		s = skipaliastoken(t);

		/* We [s] are now at the white-space -- possibly the last
		   char of the line prefix is a double-colon (:) */

		if (s == NULL) {
			/* This alias-token is invalid */
			fprintf(stderr,"Line %d: Invalid alias key token; missing colon ?\n",
				linenum);
			errflag = 1;
			continue;
		}

		/* Scan forward for additional data start */

		while (*s && (*s == '\t' || *s == ' '))
			++s;
	    
		t0 = strdup(t);
		strlower(t0); /* Lowercasify the key */
		s0 = strdup(s);
		/* Now we continue reading more input lines ... */
	}
	/* Something left to be stored ? */
	if (t0 != NULL) {
		tlen = strlen(t0) + 1;
		slen = strlen(s0) + 1;

		++count;
		totsize += slen;
		if (longest < slen)
		  longest = slen;

		if (uc_key)
		  strupper(t0); /* Uppercasify the key */
		if (lc_key)
		  strlower(t0); /* Lowercasify the key */

		(void) store_db(dbf, typ, 0, linenum,
				t0, tlen, s0, slen);
		if (t0) free(t0);  t0 = NULL;
		if (s0) free(s0);  s0 = NULL;
	}
	if (!silent)
	  fprintf(stdout, "%d aliases, longest %d bytes, %ld bytes total\n",
		  count, longest, totsize);
	return errflag;
}

int create_keyed_dbase(infile, dbf, typ)
FILE *infile;
void *dbf;
const int typ;
{
	int tlen, slen, llen;
	char *s, *t;
	int linenum = 0;
	int errflag = 0;

	while ((llen = zgetline(infile)) != 0) {
		++linenum;
		if (zlinebuf[llen-1] != '\n') {
			/* Eh ? No line ending newline ?
			   Ah well, there is always at least one byte
			   of space after the read block. */
			++llen;
			fprintf(stderr, "input file lacking trailing newline, corrupted file ?\n");
		}
		zlinebuf[llen-1] = '\0';

		if (*zlinebuf == '#')
			continue;	/* Comment! */

		/* Scan first white-space separated token,
		   point its start with t! */

		t = zlinebuf;
		while (*t == '\t' || *t == ' ')
			++t;

		if (*t == 0)
			continue;		/* Blank line! */
		if (*t == '#')
			continue;		/* Comment.. */


		s = t;
		/* Scan over the non-LWSP text */
		while (*s && *s != '\t' && *s != ' ')
			++s;
		/* Stopped without line-end NIL ?  Trunc, and advance! */
		if (*s)
			*s++ = 0;

		/* Scan forward, if we have some LWSP here, and then more data ? */
		while (*s && (*s == '\t' || *s == ' '))
			++s;
	    
		if (uc_key)
		  strupper(t); /* Uppercasify the key */
		if (lc_key)
		  strlower(t); /* Lowercasify the key */
	    
		tlen = strlen(t) + 1;
		slen = strlen(s) + 1;
		if (store_db(dbf, typ, 0, linenum,
			     t, tlen, s, slen) < 0) {
		  errflag = 1; /* Duplicate ?? */
		  break;
		}
	}
	return errflag;
}


int main(argc, argv)
int argc;
char *argv[];
{
    char *dbasename = NULL;
    FILE *infile = NULL;
    int c, rc;
    int typ = 0;
#ifdef HAVE_NDBM
    DBM *ndbmfile = NULL;
#endif
#ifdef HAVE_GDBM
    GDBM_FILE gdbmfile = NULL;
#endif
#ifdef HAVE_DB
    DB *dbfile = NULL;
#endif
    char *dbtype = NULL;
    void *dbf = NULL;
    char *argv0 = argv[0];
    int err;

    progname = argv[0];

    while ((c = getopt(argc, argv, "Aalpsuv")) != EOF) {
	switch (c) {
	case 'l':
	    lc_key = 1;
	    break;
	case 'u':
	    uc_key = 1;
	    break;
	case 'A':
	    append_mode = 1;
	    break;
	case 'a':
	    aliasinput = 1;
	    break;
	case 'p':
	    policyinput = 1;
	    break;
	case 's':
	    silent = 1;
	    break;
	case 'v':
	    verbose = 1;
	    break;
	default:
	    break;
	}
    }

    /* Usage: */
    /*  makedb [-Aap] dbtype database.name [infilename|-] */
    /* argv[] 0    1      2           3          4           */

    /* printf("optind = %d, argc = %d\n", optind, argc); */

    if ((argc - optind) < 2)
	usage(argv0, "too few arguments", 0);
    if ((argc - optind) > 3)
	usage(argv0, "too many arguments", 0);
    dbasename = argv[optind + 1];


    if ((argc - optind) == 3) {
	if (strcmp(argv[optind + 2], "-") == 0)
	    infile = stdin;
	else
	    infile = (FILE *) fopen(argv[optind + 2], "r");
    } else
	infile = stdin;
    dbtype = argv[optind];

    if (infile == NULL)
	usage(argv0, "bad infile", errno);

    typ = 0;
#ifdef HAVE_NDBM
    if (cistrcmp(dbtype, "ndbm") == 0)
	typ = 1;
#endif
#ifdef HAVE_GDBM
    if (cistrcmp(dbtype, "gdbm") == 0)
	typ = 2;
#endif
#ifdef HAVE_DB
    if (cistrcmp(dbtype, "btree") == 0)
	typ = 3;
    if (cistrcmp(dbtype, "bhash") == 0)
	typ = 4;
#endif

    switch (typ) {
    case 0:
	usage(argv0, "unknown dbtype", 0);
	break;

#ifdef HAVE_NDBM
    case 1:
	ndbmfile = dbm_open(dbasename, O_RDWR | O_CREAT | O_TRUNC, 0644);
	dbf = ndbmfile;
	break;
#endif

#ifdef HAVE_GDBM
    case 2:
	/* Play loose .. don't do syncs while writing */
	dbasename = strcpy(malloc(strlen(dbasename) + 8), dbasename);
	strcat(dbasename, ".gdbm");	/* ALWAYS append this */
	gdbmfile = gdbm_open(dbasename, 0, GDBM_NEWDB | GDBM_FAST, 0644, NULL);
	dbf = gdbmfile;
	break;
#endif
#ifdef HAVE_DB
#if defined(HAVE_DB3) || defined(HAVE_DB4) || defined(HAVE_DB5)

    case 3:
	dbasename = strcpy(malloc(strlen(dbasename) + 8), dbasename);
	strcat(dbasename, ".db");	/* ALWAYS append this */

	dbfile = NULL;
	err = db_create(&dbfile, NULL, 0);
	if (! err)
	  err = dbfile->open(dbfile,
#if ((DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 1)) || (DB_VERSION_MAJOR > 4)
			     NULL, /* TXN id was added at SleepyDB 4.1 */
#endif
			     dbasename, NULL, DB_BTREE,
			     DB_CREATE|DB_TRUNCATE, 0644);
	if (!err)
	  dbf = dbfile;
	break;

    case 4:

	dbasename = strcpy(malloc(strlen(dbasename) + 8), dbasename);
	strcat(dbasename, ".db");	/* ALWAYS append this */

	dbfile = NULL;
	err = db_create(&dbfile, NULL, 0);
	if (! err)
	  err = dbfile->open(dbfile,
#if ((DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 1)) || (DB_VERSION_MAJOR > 4)
			     NULL, /* TXN id was added at SleepyDB 4.1 */
#endif
			     dbasename, NULL, DB_HASH,
			     DB_CREATE|DB_TRUNCATE, 0644);
	if (!err)
	  dbf = dbfile;
	break;

#else
#if defined(HAVE_DB2)
    case 3:

	dbasename = strcpy(malloc(strlen(dbasename) + 8), dbasename);
	strcat(dbasename, ".db");	/* ALWAYS append this */

	dbfile = NULL;
	err = db_open(dbasename, DB_BTREE,  DB_CREATE|DB_TRUNCATE,
		      0644, NULL, NULL, &dbfile);
	if (! err)
	  dbf = dbfile;
	break;

    case 4:

	dbasename = strcpy(malloc(strlen(dbasename) + 8), dbasename);
	strcat(dbasename, ".db");	/* ALWAYS append this */

	dbfile = NULL;
	err = db_open(dbasename, DB_HASH,  DB_CREATE|DB_TRUNCATE,
		      0644, NULL, NULL, &dbfile);
	if (! err)
	  dbf = dbfile;
	break;
#else
    case 3:
	dbasename = strcpy(malloc(strlen(dbasename) + 8), dbasename);
	strcat(dbasename, ".db");	/* ALWAYS append this */

	dbfile = dbopen(dbasename, O_RDWR | O_CREAT | O_TRUNC, 0644,
			DB_BTREE, NULL);
	dbf = dbfile;
	break;

    case 4:
	dbasename = strcpy(malloc(strlen(dbasename) + 8), dbasename);
	strcat(dbasename, ".db");	/* ALWAYS append this */

	dbfile = dbopen(dbasename, O_RDWR | O_CREAT | O_TRUNC, 0644,
			DB_HASH, NULL);
	dbf = dbfile;
	break;
#endif
#endif
#endif
    }
    if (dbf == NULL)
	usage(argv0, "Can't open dbase file", errno);

    initzline(BUFSIZ);

    if (policyinput)
	    rc = create_policy_dbase(infile, dbf, typ);
    else if (aliasinput)
	    rc = create_aliases_dbase(infile, dbf, typ);
    else
	    rc = create_keyed_dbase(infile, dbf, typ);

    switch (typ) {
#ifdef HAVE_NDBM
    case 1:
      dbm_close(ndbmfile);
      break;
#endif
#ifdef HAVE_GDBM
    case 2:
      gdbm_close(gdbmfile);
      break;
#endif
#ifdef HAVE_DB
    case 3: case 4:
      (dbfile->sync) (dbfile, 0);
#if defined(HAVE_DB_CLOSE2)
      (dbfile->close) (dbfile, 0);
#else
      (dbfile->close) (dbfile);
#endif
      break;
#endif
    }  /* end of .. switch(typ) .. */

    if (store_errors) {
      fprintf(stderr,"STORE ERRORS DURING DATABASE WRITE!\n");
      rc = 1;
    }

    return (rc ? 1 : 0);
}
