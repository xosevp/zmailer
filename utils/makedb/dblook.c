/* Copyright 1993-2002 - Matti Aarnio <mea@nic.funet.fi>
   This will be free software, but only when it is finished.

   The way the Zmailer uses DBM entries is by using strings with
   their terminating NULL as keys, and as data..  Thus the length
   is strlen(string)+1, not strlen(string) !
*/

#include "hostenv.h"
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

#include <errno.h>
extern int errno;

extern void usage __((const char *, const char *, int));
void
usage(av0,err,errn)
const char *av0, *err;
int errn;
{
  fprintf(stderr,"Usage: %s [-dump|-policydump] dbtype database.name [key]\n",av0);
  fprintf(stderr,"  Dbtypes are:");
#ifdef HAVE_NDBM
  fprintf(stderr," ndbm");
#endif
#ifdef HAVE_GDBM
  fprintf(stderr," gdbm");
#endif
#ifdef HAVE_DB
  fprintf(stderr," btree bhash");
#endif
  fprintf(stderr,"\n");
#ifdef HAVE_NDBM
  fprintf(stderr,"  (NDBM appends  .pag, and .dir  into the actual db file names..)\n");
#endif
#ifdef HAVE_GDBM
  fprintf(stderr,"  (GDBM  DOES NOT append .gdbm  into the actual db file name..)\n");
#endif
#ifdef HAVE_DB
  fprintf(stderr,"  (BTREE DOES NOT append  .db   into the actual db file name..)\n");
  fprintf(stderr,"  (BHASH appends .pag, and .dir into actual db file names..)\n");
#endif
  fprintf(stderr," Error now: %s", err);
  fprintf(stderr,", errno=%d (%s)", errn, strerror(errn));
  fprintf(stderr,"\n");
  exit (1);
}

static int imax(a,b)
     int a, b;
{
  if (a > b)
    return a;
  return b;
}


#define _POLICYTEST_INTERNAL_
#include "policy.h"


/* KK() and KA() macroes are at "policy.h" */

static char *showkey __((const char *key));
static char *showkey(key)
const char *key;
{
    static char buf[256];

    if (key[1] != P_K_IPv4 && key[1] != P_K_IPv6) {
	if (strlen(key+2) > (sizeof(buf) - 20))
	    sprintf(buf,"%s", "<too long name>");
	else
	    sprintf(buf,"%s", key+2);
    } else
      if (key[1] == P_K_IPv4)
	sprintf(buf,"[%u.%u.%u.%u]/%d",
		key[2] & 0xff, key[3] & 0xff, key[4] & 0xff, key[5] & 0xff,
		key[6] & 0xff);
      else
	sprintf(buf,"[ipv6.%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x]/%d",
		key[2] & 0xff, key[3] & 0xff, key[4] & 0xff, key[5] & 0xff,
		key[6] & 0xff, key[7] & 0xff, key[8] & 0xff, key[9] & 0xff,
		key[10] & 0xff, key[11] & 0xff, key[12] & 0xff, key[13] & 0xff,
		key[14] & 0xff, key[15] & 0xff, key[16] & 0xff, key[17] & 0xff,
		key[18] & 0xff);
    return buf;
}



static char *showattr __((const char *key));
static char *showattr(key)
const char *key;
{
    static char buf[500];
    char *name = KA(key[1]);
    if (key[1] == P_A_ALIAS) name = "=";
    sprintf(buf, "%s",  name);
    return buf;
}

static void showpolicydata __((FILE *, const void *, int));
static void showpolicydata(fp, dp, len)
     FILE *fp;
     const void *dp;
     int len;
{
  fprintf(fp, " %s \"%s\"", showattr(dp), (char *)dp+2);
}


void dumpit(fp, flag, keyptr, keylen, datptr, datlen)
     FILE *fp;
     int flag;
     void *keyptr, *datptr;
     int keylen, datlen;
{
  if (flag == 1) {
    if (((char*)keyptr)[imax(0, keylen - 1)] == 0)
      fwrite(keyptr, 1, imax(0, keylen - 1), fp);
    else
      fwrite(keyptr, 1, keylen, fp);
    if (datptr != NULL) {
      putc('\t',fp);
      if (((char*)datptr)[imax(0, datlen - 1)] == 0)
	fwrite(datptr, 1, imax(0, datlen - 1), fp);
      else
	fwrite(datptr, 1, datlen, fp);
    }
    putc('\n',fp);
  } else {
    unsigned char *dp = datptr;

    fprintf(fp, "%s\t", showkey(keyptr));

    while (datlen > 0) {
      int len = *dp;
      if (len > datlen) len = datlen;
      showpolicydata(fp, dp, len);
      datlen -= len;
      dp += len;
    }
    putc('\n',fp);
  }
}

int
main(argc,argv)
int argc;
char *argv[];
{
  char *dbasename = NULL;
  char *argv0 = argv[0];
  int dumpflag = 0;

  if (argc != 4) usage(argv0,"wrong number of arguments",0);

  if (strcmp(argv[1],"-dump") == 0) {
    dumpflag = 1;
    ++argv;
  }
  if (strcmp(argv[1],"-policydump") == 0) {
    dumpflag = 2;
    ++argv;
  }

  dbasename = argv[2];
#ifdef HAVE_NDBM
  if (strcmp(argv[1],"ndbm")==0) {
    DBM *Ndbmfile;
    Ndatum key;
    Ndatum result;
    Ndbmfile = dbm_open(dbasename, O_RDONLY, 0644);

    if (!Ndbmfile) {
      fprintf(stderr,"Failed to open '%s' NDBM-dbase\n",dbasename);
      return 1;
    }

    if (dumpflag) {
      key = dbm_firstkey(Ndbmfile);
      while (key.dptr != NULL) {
	result = dbm_fetch(Ndbmfile, key);
	dumpit(stdout, dumpflag, key.dptr, key.dsize, result.dptr, result.dsize);
	key = dbm_nextkey(Ndbmfile);
      }
    } else {
      key.dptr = argv[3];
      key.dsize = strlen(argv[3]) +1;

      result = dbm_fetch(Ndbmfile,key);

      if (result.dptr == NULL) {
	fprintf(stderr,"Key %s not found\n",argv[3]);
	return 2;
      }
      printf("siz:%d, dat: %s\n", result.dsize, result.dptr);
    }

    dbm_close(Ndbmfile);

    return 0;
  }
#endif /* NDBM */
#ifdef HAVE_GDBM
  if (strcmp(argv[1],"gdbm")==0) {
    GDBM_FILE gdbmfile;
    Gdatum key, nextkey;
    Gdatum result;
    gdbmfile = gdbm_open(dbasename, 0, GDBM_READER, 0644, NULL);

    if (!gdbmfile) {
      fprintf(stderr,"Failed to open '%s' GDBM-dbase (do remember to add file suffix!)\n",dbasename);
      return 1;
    }

    if (dumpflag) {
      key = gdbm_firstkey(gdbmfile);
      while (key.dptr != NULL) {
	result = gdbm_fetch(gdbmfile, key);
	dumpit(stdout, dumpflag, key.dptr, key.dsize, result.dptr, result.dsize);
	if (result.dptr) free(result.dptr);
	nextkey = gdbm_nextkey(gdbmfile, key);
	free(key.dptr);
	key = nextkey;
      }
    } else {
      key.dptr = argv[3];
      key.dsize = strlen(argv[3]) +1;

      result = gdbm_fetch(gdbmfile,key);

      if (result.dptr == NULL) {
	fprintf(stderr,"Key %s not found\n",argv[3]);
	return 2;
      }
      printf("siz:%d, dat: %s\n",result.dsize,result.dptr);
    }

    gdbm_close(gdbmfile);

    return 0;
  }
#endif /* GDBM */

#ifdef HAVE_DB

#if defined(HAVE_DB3) || defined(HAVE_DB4) || defined(HAVE_DB5)

  if (strcmp(argv[1],"btree")==0) {
    DB *dbfile;
    DBT key;
    DBT result;
    int rc;

    dbfile = NULL;
    rc = db_create(&dbfile, NULL, 0);
    if (rc == 0)
      rc = dbfile->open(dbfile,
#if ((DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 1)) || (DB_VERSION_MAJOR > 4)
			NULL, /* TXN id was added at SleepyDB 4.1 */
#endif
			dbasename, NULL, DB_BTREE,
			DB_RDONLY, 0644);


    if (!dbfile || rc != 0) {
      fprintf(stderr,"Failed to open '%s' BTREE-dbase (try with whole filename?)\n",dbasename);
      return 1;
    }

    if (dumpflag) {
      DBC *curs;
      memset(&curs, 0, sizeof(curs));
      rc = (dbfile->cursor)(dbfile, NULL, &curs, 0);
      if (!rc) {
	memset(&key, 0, sizeof(key));
	memset(&result, 0, sizeof(key));
	rc = (curs->c_get)(curs, &key, &result, DB_FIRST);
      }
      if (rc) fprintf(stderr,"cursor errno=%d (%s)\n",rc, db_strerror(rc));
      while ( rc == 0 ) {
	dumpit(stdout, dumpflag, key.data, key.size, result.data, result.size);
	rc = (curs->c_get)(curs, &key, &result, DB_NEXT);
      }
      if (curs) (curs->c_close)(curs);
    } else {
      memset(&key,    0, sizeof(key));
      memset(&result, 0, sizeof(result));
      key.data = argv[3];
      key.size = strlen(argv[3]) +1;

      rc = (dbfile->get)(dbfile, NULL, &key, &result, 0);

      if (rc != 0) {
	fprintf(stderr,"Key %s not found\n",argv[3]);
	return 2;
      }
      printf("siz:%ld, dat: %s\n", (long)result.size, (char*)result.data);
    }

    (dbfile->close)(dbfile, 0);

    return 0;
  }

  if (strcmp(argv[1],"bhash")==0) {
    DB *dbfile;
    DBT key;
    DBT result;
    int rc;

    dbfile = NULL;
    rc = db_create(&dbfile, NULL, 0);
    if (rc == 0)
      rc = dbfile->open(dbfile,
#if ((DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 1)) || (DB_VERSION_MAJOR > 4)
			NULL, /* TXN id was added at SleepyDB 4.1 */
#endif
			dbasename, NULL, DB_HASH,
			DB_RDONLY, 0644);


    if (!dbfile || rc != 0) {
      fprintf(stderr,"Failed to open '%s' BHASH-dbase (try with whole filename)\n",dbasename);
      return 1;
    }

    if (dumpflag) {
      DBC *curs;
      memset(&curs, 0, sizeof(curs));
      rc = (dbfile->cursor)(dbfile, NULL, &curs, 0);
      memset(&key, 0, sizeof(key));
      memset(&result, 0, sizeof(key));
      rc = (curs->c_get)(curs, &key, &result, DB_FIRST);
      while ( rc == 0 ) {
	dumpit(stdout, dumpflag, key.data, key.size, result.data, result.size);
	rc = (curs->c_get)(curs, &key, &result, DB_NEXT);
      }
      (curs->c_close)(curs);
    } else {
      memset(&key,    0, sizeof(key));
      memset(&result, 0, sizeof(result));
      key.data = argv[3];
      key.size = strlen(argv[3]) +1;

      rc = (dbfile->get)(dbfile, NULL, &key, &result, 0);

      if (rc != 0) {
	fprintf(stderr,"Key %s not found\n",argv[3]);
	return 2;
      }
      printf("siz:%ld, dat: %s\n",(long)result.size,(char*)result.data);
    }

    (dbfile->close)(dbfile, 0);

    return 0;
  }

#else
#if defined(HAVE_DB2)

  if (strcmp(argv[1],"btree")==0) {
    DB *dbfile;
    DBT key;
    DBT result;
    int rc;

    dbfile = NULL;
    db_open(dbasename, DB_BTREE, DB_RDONLY, 0644, NULL, NULL, &dbfile);

    if (!dbfile) {
      fprintf(stderr,"Failed to open '%s' BTREE-dbase (try with whole filename?)\n",dbasename);
      return 1;
    }

    if (dumpflag) {
      DBC *curs;
#ifdef HAVE_DB_CURSOR4
      rc = (dbfile->cursor)(dbfile, NULL, &curs, 0);
#else
      rc = (dbfile->cursor)(dbfile, NULL, &curs);
#endif
      memset(&key, 0, sizeof(key));
      memset(&result, 0, sizeof(key));
      rc = (curs->c_get)(curs, &key, &result, DB_FIRST);
      if (rc) fprintf(stderr,"cursor errno=%d (%s)\n",rc, strerror(rc));
      while ( rc == 0 ) {
	dumpit(stdout, dumpflag, key.data, key.size, result.data, result.size);
	rc = (curs->c_get)(curs, &key, &result, DB_NEXT);
      }
      (curs->c_close)(curs);
    } else {
      memset(&key,    0, sizeof(key));
      memset(&result, 0, sizeof(result));
      key.data = argv[3];
      key.size = strlen(argv[3]) +1;

      rc = (dbfile->get)(dbfile, NULL, &key, &result, 0);

      if (rc != 0) {
	fprintf(stderr,"Key %s not found\n",argv[3]);
	return 2;
      }
      printf("siz:%ld, dat: %s\n", (long)result.size, (char*)result.data);
    }

    (dbfile->close)(dbfile, 0);

    return 0;
  }

  if (strcmp(argv[1],"bhash")==0) {
    DB *dbfile;
    DBT key;
    DBT result;
    int rc;

    dbfile = NULL;
    db_open(dbasename, DB_HASH, DB_RDONLY, 0644, NULL, NULL, &dbfile);

    if (!dbfile) {
      fprintf(stderr,"Failed to open '%s' BHASH-dbase (try with whole filename)\n",dbasename);
      return 1;
    }

    if (dumpflag) {
      DBC *curs;
#ifdef HAVE_DB_CURSOR4
      rc = (dbfile->cursor)(dbfile, NULL, &curs, 0);
#else
      rc = (dbfile->cursor)(dbfile, NULL, &curs);
#endif
      memset(&key, 0, sizeof(key));
      memset(&result, 0, sizeof(key));
      rc = (curs->c_get)(curs, &key, &result, DB_FIRST);
      while ( rc == 0 ) {
	dumpit(stdout, dumpflag, key.data, key.size, result.data, result.size);
	rc = (curs->c_get)(curs, &key, &result, DB_NEXT);
      }
      (curs->c_close)(curs);
    } else {
      memset(&key,    0, sizeof(key));
      memset(&result, 0, sizeof(result));
      key.data = argv[3];
      key.size = strlen(argv[3]) +1;

      rc = (dbfile->get)(dbfile, NULL, &key, &result, 0);

      if (rc != 0) {
	fprintf(stderr,"Key %s not found\n",argv[3]);
	return 2;
      }
      printf("siz:%ld, dat: %s\n",(long)result.size,(char*)result.data);
    }

    (dbfile->close)(dbfile, 0);

    return 0;
  }

#else /* Old BSD DB 1.* */

  if (strcmp(argv[1],"btree")==0) {
    DB *dbfile;
    DBT key;
    DBT result;
    int rc;

    dbfile = dbopen(dbasename, O_RDONLY, 0644, DB_BTREE, NULL);

    if (!dbfile) {
      fprintf(stderr,"Failed to open '%s' BTREE-dbase (use whole filenames?)\n",dbasename);
      return 1;
    }

    if (dumpflag) {
      memset(&key, 0, sizeof(key));
      memset(&result, 0, sizeof(key));
      rc = (dbfile->seq)(dbfile, &key, &result, R_FIRST);
      while ( rc == 0 ) {
	dumpit(stdout, dumpflag, key.data, key.size, result.data, result.size);
	rc = (dbfile->seq)(dbfile, &key, &result, R_NEXT);
      }
    } else {
      key.data = argv[3];
      key.size = strlen(argv[3]) +1;

      rc = (dbfile->get)(dbfile,&key,&result,0);

      if (rc != 0) {
	fprintf(stderr,"Key %s not found\n",argv[3]);
	return 2;
      }
      printf("siz:%ld, dat: %s\n", (long)result.size, (char*)result.data);
    }

    (dbfile->close)(dbfile);

    return 0;
  }

  if (strcmp(argv[1],"bhash")==0) {
    DB *dbfile;
    DBT key;
    DBT result;
    int rc;

    dbfile = dbopen(dbasename, O_RDONLY, 0644, DB_HASH, NULL);

    if (!dbfile) {
      fprintf(stderr,"Failed to open '%s' BHASH-dbase (use whole filenames?)\n",dbasename);
      return 1;
    }

    if (dumpflag) {
      memset(&key, 0, sizeof(key));
      memset(&result, 0, sizeof(key));
      rc = (dbfile->seq)(dbfile, &key, &result, R_FIRST);
      while ( rc == 0 ) {
	dumpit(stdout, dumpflag, key.data, key.size, result.data, result.size);
	rc = (dbfile->seq)(dbfile, &key, &result, R_NEXT);
      }
    } else {
      key.data = argv[3];
      key.size = strlen(argv[3]) +1;

      rc = (dbfile->get)(dbfile,&key,&result,0);

      if (rc != 0) {
	fprintf(stderr,"Key %s not found\n",argv[3]);
	return 2;
      }
      printf("siz:%ld, dat: %s\n",(long)result.size,(char*)result.data);
    }

    (dbfile->close)(dbfile);

    return 0;
  }
#endif
#endif
#endif

  usage(argv0, "Unrecognized dbformat", 0);

  return 0;
}
