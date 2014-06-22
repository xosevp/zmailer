/*
 *  policytest.c -- module for ZMailer's smtpserver
 *  By Matti Aarnio <mea@nic.funet.fi> 1997-2006
 *
 */

/*
 * TODO:
 *  - Attribute 'request' initializations for resolving
 *  - Addresses in form  <@foo:uu@dd>, <host!user>
 */

#include "hostenv.h"

#include "sleepycatdb.h"

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

#define _POLICYTEST_INTERNAL_
#include "smtpserver.h"

#ifdef HAVE_SPF2_SPF_H
#include <spf2/spf.h>
#include <spf2/spf_dns_resolv.h>
#else
#ifdef HAVE_SPF_ALT_SPF_H
#include <spf_alt/spf.h>
#include <spf_alt/spf_dns_resolv.h>
#endif
#endif

#define PICK_PA_MSG(attrib)	\
	if (state->message) free(state->message);	\
	state->message = state->messages[(attrib)];	\
	state->messages[(attrib)] = NULL

int use_spf;			/* These are in UNIX rss segment, and  */
int spf_received;		/* they will be set zero at program load */
int spf_threshold;
char *spf_localpolicy;
int spf_whitelist_use_default;

static int resolveattributes __((struct policytest *, int, struct policystate *, const unsigned char *, int));
static int  check_domain __((struct policystate *, const unsigned char *, int));
static int  check_user __((struct policystate *, const unsigned char *, int));
static int  checkaddr  __((struct policystate *, const unsigned char *));

#if defined(AF_INET6) && defined(INET6)
extern const u_char zv4mapprefix[16];
#endif

/* KK() and KA() macroes are at "policy.h" */

static char *showkey __((const unsigned char *key));
static char *showkey(key)
     const unsigned char *key;
{
    static char buf[256];

    if (key[1] != P_K_IPv4 && key[1] != P_K_IPv6) {
	if (strlen((const char*)key+2) > (sizeof(buf) - 200))
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

static char *showattr __((const unsigned char *key));
static char *showattr(key)
const unsigned char *key;
{
    static char buf[500];
    sprintf(buf,"%d/%s/'%s'", key[0], KA(key[1]), key+2);
    return buf;
}

static int valueeq __((const char *value, const char *str));
static int valueeq(value,str)
     const char *value;
     const char *str;
{
    if (!value) return 0;
    return (strcmp(value,str) == 0);
}

static char *showresults __((struct policystate *state));
static char *showresults(state)
struct policystate *state;
{
    static char buf[2000];
    int i;
    char **values=state->values;

    buf[0] = '\0';
    for (i = P_A_FirstAttr; i <= P_A_LastAttr; ++i) {
	sprintf(buf+strlen(buf),"%s ",KA(i));
	if (i == P_A_InboundSizeLimit )
	    sprintf(buf+strlen(buf),"%li ",state->maxinsize);
	else if (i == P_A_OutboundSizeLimit )
	    sprintf(buf+strlen(buf),"%li ",state->maxoutsize);
	else if (i == P_A_MaxSameIpSource )
	    sprintf(buf+strlen(buf),"%li ",state->maxsameiplimit);
	else
	    sprintf(buf+strlen(buf),"%s ",values[i] ? values[i] : ".");
    }
    return buf;
}

static void printstate __((const struct policystate *state));
static void printstate (state)
const struct policystate *state;
{
	int i;

	type(NULL,0,NULL," always_reject=%d",state->always_reject);
	type(NULL,0,NULL," always_freeze=%d",state->always_freeze);
	type(NULL,0,NULL," always_accept=%d",state->always_accept);
	type(NULL,0,NULL," full_trust=%d",   state->full_trust);
	type(NULL,0,NULL," trust_recipients=%d",state->trust_recipients);
	type(NULL,0,NULL," sender_reject=%d",state->sender_reject);
	type(NULL,0,NULL," sender_freeze=%d",state->sender_freeze);
	type(NULL,0,NULL," sender_norelay=%d",state->sender_norelay);
	type(NULL,0,NULL," relaycustnet=%d", state->relaycustnet);

	for ( i = P_A_FirstAttr; i <= P_A_LastAttr ; ++i) {
	    type(NULL,0,NULL," %s: %srequested, value=%s", KA(i),
		 (state->origrequest & (1<<i)) ? "" : "not ",
		 state->values[i]?state->values[i]:".");
	}

	type(NULL,0,NULL," maxinsize=%li", state->maxinsize);
	type(NULL,0,NULL," maxoutsize=%li", state->maxoutsize);
	type(NULL,0,NULL," maxsameiplimit=%li", state->maxsameiplimit);
}

static void mask_ip_bits __((unsigned char *, int, int));
static void mask_ip_bits(ipnum, width, maxwidth)
unsigned char *ipnum;
int width, maxwidth;
{
    int i, bytewidth, bytemaxwidth;

    bytemaxwidth = maxwidth >> 3;	/* multiple of 8 */
    bytewidth = (width + 7) >> 3;

    /* All full zero bytes... */
    for (i = bytewidth; i < bytemaxwidth; ++i)
	ipnum[i] = 0;

    /* Now the remaining byte */
    i = 8 - (width & 7);	/* Modulo 8 */

    bytewidth = width >> 3;
    if (i != 8) {
	/* Not exactly multiple-of-byte-width operand to be masked    */
	/* For 'width=31' we get now 'bytewidth=3', and 'i=1'         */
	/* For 'width=25' we get now 'bytewidth=3', and 'i=7'         */
	ipnum[bytewidth] &= (0xFF << i);
    }
}


void policydefine(relp, dbtype, dbpath)
     struct policytest **relp;
     const char *dbtype, *dbpath;
{
    struct policytest *rel = (void *) emalloc(sizeof(*rel));
    *relp = rel;
    memset(rel, 0, sizeof(*rel));
    rel->dbtype = strdup(dbtype);
    rel->dbpath = strdup(dbpath);
    rel->dbt    = _dbt_none;
}



int policyinit(state, rel, submission_mode_flags, valid_whoson)
     struct policystate *state;
     struct policytest  *rel;
     int submission_mode_flags;
     int valid_whoson;
{
    int openok;
    char *dbname;
    char *myhostname;

    if (rel == NULL)
      return 1;  /* Not defined! */

    if (debug) 
	type(NULL,0,NULL,"Policyinit call starts: submission mode: %d, valid whoson: %d",
	       submission_mode_flags, valid_whoson);

    myhostname = state->myhostname;
    memset(state, 0, sizeof(*state));
    state->myhostname = myhostname;

    /*
     * state->implied_submission_mode = (submission_mode_flags & 1); ???
     */

    state->PT = rel; /* Store the policytest dataset into state pointer.. */

#ifdef HAVE_NDBM
    if (cistrcmp(rel->dbtype, "ndbm") == 0)
	rel->dbt = _dbt_ndbm;
#endif
#ifdef HAVE_GDBM
    if (cistrcmp(rel->dbtype, "gdbm") == 0)
	rel->dbt = _dbt_gdbm;
#endif
#ifdef HAVE_DB
    if (cistrcmp(rel->dbtype, "btree") == 0)
	rel->dbt = _dbt_btree;
    if (cistrcmp(rel->dbtype, "bhash") == 0)
	rel->dbt = _dbt_bhash;
#if defined(DB_RPCCLIENT)
    if (cistrcmp(rel->dbtype, "sleepyrpc") == 0)
	rel->dbt = _dbt_sleepyrpc;
#endif
#endif
    if (rel->dbt == _dbt_none) {
	/* XX: ERROR! Unknown/unsupported dbtype! */
      state->PT = NULL;
      return 1;
    }
    openok = 0;
#ifdef HAVE_ALLOCA
    dbname = (char*)alloca(strlen(rel->dbpath) + 8);
#else
    dbname = (char*)emalloc(strlen(rel->dbpath) + 8);
#endif
    switch (rel->dbt) {
#ifdef HAVE_NDBM
    case _dbt_ndbm:
	/*
	   rel->ndbm = dbm_open((char*)rel->dbpath, O_RDWR|O_CREAT|O_TRUNC, 0644);
	 */
	strcpy(dbname, rel->dbpath);
	rel->ndbm = dbm_open(dbname, O_RDONLY, 0644);
	openok = (rel->ndbm != NULL);
	break;
#endif
#ifdef HAVE_GDBM
    case _dbt_gdbm:
	/* Append '.gdbm' to the name */
	sprintf(dbname, "%s.gdbm", rel->dbpath);
	rel->gdbm = gdbm_open(dbname, 0, GDBM_READER, 0644, NULL);
	openok = (rel->gdbm != NULL);
	break;
#endif
#ifdef HAVE_DB
#if defined(DB_RPCCLIENT)
    case _dbt_sleepyrpc:
      {
	DB_ENV *env;

	/* FIXME:FIXME:FIXME:
	   Treat supplied  rel->dbpath  as host into for
	   SleepyDB rpc server. Need also to have db name in there ??
	   Or more parameters by listing them in separate file that
	   is named in rel->dbpath  and parsed ?? 
	    - RPChost
	    - server timeout
	    - client timeout
	    - homedir in server
	    - database (file)name
	*/
	
        openok = db_env_create(& env, DB_RPCCLIENT);
	/* XX: 0 == ok */
	rel->db_._db_env = env;

	openok = env->set_rpc_server( env, NULL, rel->dbpath,
				      0 /* cl_timeout */, 0 /* sv_timeout */,
				      0 );
	/* XX: 0 == ok */

	openok = env->open(env, rel->dbpath, DB_JOINENV, 0); /* FIXME!FIXME! */
	/* XX: 0 == ok */

	openok = db_create(& rel->sleepyrpc, env, 0);
	/* XX: 0 == ok */


	/* Append '.db' to the name */
	sprintf(dbname, "%s.db", rel->dbpath);

	openok = rel->sleepyrpc->open(rel->sleepyrpc,
#if ((DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 1)) || (DB_VERSION_MAJOR > 4)
				      NULL, /* TXN id was added at SleepyDB 4.1 */
#endif
				      dbname, NULL,  DB_BTREE,
				      DB_RDONLY, 0);

	break;
      }
#endif

    case _dbt_btree:
	/* Append '.db' to the name */
	sprintf(dbname, "%s.db", rel->dbpath);

#if defined(HAVE_DB3) || defined(HAVE_DB4) || defined(HAVE_DB5)

	rel->btree = NULL;
	openok = db_create(&rel->btree, NULL, 0);
	if (openok == 0)
	  openok = rel->btree->open(rel->btree,
#if ((DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 1)) || (DB_VERSION_MAJOR > 4)
				    NULL, /* TXN id was added at SleepyDB 4.1 */
#endif
				    dbname, NULL,  DB_BTREE,
				    DB_RDONLY, 0);
	if (debug && openok)
	  type(NULL,0,NULL," btree->open('%s',BTREE, RDONLY) ret=%d",dbname,openok);
	openok = !openok;

#else
#if defined(HAVE_DB2)

	rel->btree = NULL;
#ifndef DB_RDONLY
# define DB_RDONLY O_RDONLY
#endif
	openok = db_open(dbname, DB_BTREE, DB_RDONLY, 0644,
			 NULL, NULL, &rel->btree);
	openok = !openok;
#else /* HAVE_DB1 */
	rel->btree = dbopen(dbname, O_RDONLY, 0644, DB_BTREE, NULL);
	openok = (rel->btree != NULL);
#endif
#endif
	break;

    case _dbt_bhash:
	/* Append '.db' to the name */
	sprintf(dbname, "%s.dbh", rel->dbpath);

#if defined(HAVE_DB3) || defined(HAVE_DB4) || defined(HAVE_DB5)

	rel->bhash = NULL;
	openok = db_create(&rel->bhash, NULL, 0);
	if (openok == 0)
	  openok = rel->bhash->open(rel->bhash,
#if ((DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 1)) || (DB_VERSION_MAJOR > 4)
				    NULL, /* TXN id was added at SleepyDB 4.1 */
#endif
				    dbname, NULL, DB_HASH,
				    DB_RDONLY, 0);
	if (debug && openok)
	  type(NULL,0,NULL," bhash->open('%s',BHASH, RDONLY) ret=%d",dbname,openok);
	openok = !openok;

#else
#if defined(HAVE_DB2)

	rel->bhash = NULL;
#ifndef DB_RDONLY
# define DB_RDONLY O_RDONLY
#endif
	openok = db_open(dbname, DB_HASH, DB_RDONLY, 0644,
			 NULL, NULL, &rel->bhash);
	openok = !openok;
#else /* HAVE_DB1 */
	rel->bhash = dbopen(rel->dbpath, O_RDONLY, 0644, DB_HASH, NULL);
	openok = (rel->bhash != NULL);
#endif
#endif
	break;
#endif
    default:
	break;
    }
    if (!openok) {
	/* ERROR!  Could not open the database! */
      if (debug) {
	type(NULL,0,NULL," ERROR!  Could not open the database file '%s'; errno=%d!",
	       dbname, errno);
	fflush(stdout);
      }
      state->PT = NULL;

#ifndef HAVE_ALLOCA
      free(dbname);
#endif
      return 2;
    }
#ifndef HAVE_ALLOCA
    free(dbname);
#endif

#ifdef HAVE_WHOSON_H
    state->valid_whoson = valid_whoson;
#endif

#ifdef Z_CHECK_SPF_DATA
    state->check_spf  = 0;
    state->spf_passed = 0;
#endif
    state->maxsameiplimit = -1;
    return 0;
}

#ifdef Z_CHECK_SPF_DATA
void initialize_spf(state)
    struct policystate *state;
{
    if (state->spf_passed) return;
    state->spf_passed=1;

    state->check_spf=1;

    if ((state->spfcid=SPF_create_config()) == NULL) {
        type(NULL,0,NULL," SPF_create_config() failed");
        state->check_spf=0;
        return;
    }

    if ((state->spfdcid=SPF_dns_create_config_resolv(NULL, 0)) == NULL) {
	type(NULL,0,NULL," SPF_dns_create_config() failed");
	state->check_spf=0;
	return;
    }

    SPF_init_c_results(&state->local_policy);
    if (SPF_compile_local_policy(state->spfcid,
				 spf_localpolicy,
				 spf_whitelist_use_default,
				 &state->local_policy)) {
	type(NULL,0,NULL," SPF_compile_local_policy() failed: %s",
	     state->local_policy.err_msg);
	free(spf_localpolicy);
	state->check_spf=0;
	return;
    }
    if (debug)
	type(NULL,0,NULL," SPF local_policy: %s",spf_localpolicy);
#warning "strange looking  free(spf_localpolicy)  call here!"
    free(spf_localpolicy); /* FIXME??FIXME??FIXME?? */

    SPF_set_local_policy(state->spfcid,state->local_policy);
}
#endif



/* Do the actual query - return pointer to the result record */
static void *dbquery __((struct policytest *, const void *, const int, int *));

static void *dbquery(rel, qptr, qlen, rlenp)
     struct policytest *rel;
     const void *qptr;
     const int qlen;
     int *rlenp;			/* result length ptr ! */
{
    char *buffer;
#ifdef HAVE_NDBM
    Ndatum Nkey, Nresult;
#endif
#ifdef HAVE_GDBM
    Gdatum Gkey, Gresult;
#endif
#ifdef HAVE_DB
    DBT Bkey, Bresult;
    int rc;
#endif


    switch (rel->dbt) {
#ifdef HAVE_NDBM
    case _dbt_ndbm:

	Nkey.dptr = (char *) qptr;
	Nkey.dsize = qlen;

	Nresult = dbm_fetch(rel->ndbm, Nkey);
	if (Nresult.dptr == NULL)
	    return NULL;

	buffer = (char *) emalloc(Nresult.dsize);
	memcpy(buffer, Nresult.dptr, Nresult.dsize);

	*rlenp = Nresult.dsize;
	return buffer;

	break; /* some compilers complain, some produce bad code
		  without this... */
#endif
#ifdef HAVE_GDBM
    case _dbt_gdbm:

	Gkey.dptr = (void *) qptr;
	Gkey.dsize = qlen;

	Gresult = gdbm_fetch(rel->gdbm, Gkey);

	/* gdbm_fetch allocates memory for return data: Gresult.dptr
	   Must be freed later. */

	*rlenp = Gresult.dsize;
	return Gresult.dptr;

	break; /* some compilers complain, some produce bad code
		  without this... */
#endif

#ifdef HAVE_DB
#ifdef DB_RPCCLIENT
    case _dbt_sleepyrpc:

	memset(&Bkey,    0, sizeof(Bkey));
	memset(&Bresult, 0, sizeof(Bresult));

	Bkey.data = (void *) qptr;
	Bkey.size = qlen;

#ifdef DB_INIT_TXN
	rc = (rel->sleepyrpc->get) (rel->sleepyrpc, NULL, &Bkey, &Bresult, 0);
#else
	rc = (rel->sleepyrpc->get) (rel->sleepyrpc, &Bkey, &Bresult, 0);
#endif
	if (rc != 0)
	    return NULL;

	buffer = (char *) emalloc(Bresult.size);
	memcpy(buffer, Bresult.data, Bresult.size);

	*rlenp = Bresult.size;
	return buffer;

	break; /* some compilers complain, some produce bad code
		  without this... */
#endif

    case _dbt_btree:

	memset(&Bkey,    0, sizeof(Bkey));
	memset(&Bresult, 0, sizeof(Bresult));

	Bkey.data = (void *) qptr;
	Bkey.size = qlen;

#ifdef DB_INIT_TXN
	rc = (rel->btree->get) (rel->btree, NULL, &Bkey, &Bresult, 0);
#else
	rc = (rel->btree->get) (rel->btree, &Bkey, &Bresult, 0);
#endif
	if (rc != 0)
	    return NULL;

	buffer = (char *) emalloc(Bresult.size);
	memcpy(buffer, Bresult.data, Bresult.size);

	*rlenp = Bresult.size;
	return buffer;

	break; /* some compilers complain, some produce bad code
		  without this... */

    case _dbt_bhash:

	memset(&Bkey,    0, sizeof(Bkey));
	memset(&Bresult, 0, sizeof(Bresult));

	Bkey.data = (void *) qptr;
	Bkey.size = qlen;

#ifdef DB_INIT_TXN
	rc = (rel->bhash->get) (rel->bhash, NULL, &Bkey, &Bresult, 0);
#else
	rc = (rel->bhash->get) (rel->bhash, &Bkey, &Bresult, 0);
#endif
	if (rc != 0)
	    return NULL;

	buffer = (char *) emalloc(Bresult.size);
	memcpy(buffer, Bresult.data, Bresult.size);

	*rlenp = Bresult.size;
	return buffer;

	break; /* some compilers complain, some produce bad code
		  without this... */
#endif
    default:
	break;
    }
    return NULL;
}



/******************************************************************************
 * Function: resolveattributes()
 *
 *       recursions - Max recursive calls for parsing aliases.
 *    state.request - These bit flags say which attributes are checked.
 * state.values[]   - Attribute values are stored here. Both are indexed
 *                    according to the attribute constants. (P_A_...)
 *              key - Pointer to search record. Binary address, ascii alias or
 *                    ascii domain name.
 *             init - Init flag. Give value 1. Value 0 when called recursively
 *                    by itself.
 * -------------
 * Returns 0, when it has found something
 *****************************************************************************/

static int resolveattributes(rel, recursions, state, key, init)
     struct policytest *rel;
     int recursions;
     struct policystate *state;
     const unsigned char *key;
     int init;
{
    unsigned char *str, *str_base;
    int rlen, result, interest;
    char *msgstr = NULL;

    if (init) {
	/* First call of this function. Not called recursively. */
	/* Zero return value array. */
	int i;
	for (i = 0; i <= P_A_LastAttr; ++i) {
	  if (state->values[i])   free(state->values[i]);
	  if (state->messages[i]) free(state->messages[i]);
	}
	memset(state->values, 0, sizeof(state->values));
	memset(state->messages, 0, sizeof(state->messages));

	state->origrequest = state->request;
    }
    --recursions;

    if (debug)
       type(NULL,0,NULL," Key: %s", showkey(key));
/*
    if (key[1] != P_K_IPv4 && key[1] != P_K_IPv6) {
	if (debug)
	  type(NULL,0,NULL," Key: %d/%d/%s", key[0],key[1],key+2);
    } else
      if (debug)
	type(NULL,0,NULL," Key: %u.%u.%u.%u", key[2], key[3], key[4], key[5]);
*/

    rlen = 0; /* <-- Placate compiler.. */
    str_base = str = (unsigned char *) dbquery(rel, &key[0], key[0], &rlen);

    /* str[0]    - attribute list lenght
       str[1]    - attribute numeric value
       str[2...] - attribute flag string    */

    if (str == NULL) {
      if (debug)
	type(NULL,0,NULL,"  query failed");
      return -1;
    }
    /* Scan trough attribute list. Call resolveattributes recursively
       if aliases is found */

    while (rlen > 3) {

	if (str[0] < 3) {
	  if (debug)
	    type(NULL,0,NULL," Bad length of attrbute, under 3 bytes!  %d", str[0]);
	  break; /* BAD ATTRIBUTE! */
	}

	/* Attribute */
	if (debug)
	  type(NULL,0,NULL,"   Attribute: %s", showattr(str));

	/* Alias */
	if (str[1] == P_A_ALIAS) {
	    /* Do not continue if max recursions reached. */
	    if (recursions < 0) {
	      if (debug)
		type(NULL,0,NULL," Max recursions reached.");
	    } else {
	      unsigned char pbuf[256];

	      if (debug)
		type(NULL,0,NULL," Alias-recursion: %d", recursions);

	      strncpy((char*)pbuf+2, (const char *) str+2, sizeof(pbuf)-3);
	      pbuf[ sizeof(pbuf)-1 ] = 0;

	      strlower((char*)pbuf+2);
	      pbuf[0] = strlen((const char*) str+2) + 3;
	      pbuf[1] = P_K_TAG;
	      result = resolveattributes(rel, recursions, state, pbuf, 0);
	    }
	    rlen -= str[0];
	    str  += str[0];
	    continue;
	}

	if (str[1] == P_A_MESSAGE) {
	  if (msgstr) free(msgstr);
	  msgstr = strdup((const char *)str+2);
	  goto nextattr;
	}

	interest = 1 << str[1];	/* Convert attrib. num. value into flag bit */
	if ((interest & state->request) == 0) {
	    /* Not interested in this attribute, skip into next. */
	    if (debug)
	      type(NULL,0,NULL,"     not interested, skipped...");

	    goto nextattr;
	} else {
	    /* Mask it off. */
	    state->request &= ~interest;
	}

	if (P_A_FirstAttr <= str[1] && str[1] <= P_A_LastAttr) {
	  /* If a message was given in previous attribute, pick it! */
	  state->messages[0xFF & (str[1])] = msgstr;
	  msgstr = NULL;
	}

	if (str[1] == P_A_InboundSizeLimit) {

	  sscanf((char *)str+2,"%li", &state->maxinsize);
	  goto nextattr;

	} else if (str[1] == P_A_OutboundSizeLimit) {

	  sscanf((char *)str+2,"%li", &state->maxoutsize);
	  goto nextattr;

	} else if (str[1] == P_A_MaxSameIpSource) {

	  sscanf((char *)str+2,"%li", &state->maxsameiplimit);
	  goto nextattr;

	} else if ((str[2] != '+' && str[2] != '-') &&
		   !state->values[str[1] & 0xFF]) {

	  /* Supply suffix domain (set), e.g.:
	         RBL.MAPS.VIX.COM,DUL.MAPS.VIX.COM
	     whatever you want ... */

	  state->values[str[1] & 0xFF] = strdup((const char *)str + 2);

	} else if (str[2] != '+' && str[2] != '-') {

	  if (debug)
	    type(NULL,0,NULL," Unknown flag: %s", &str[2]);
	  goto nextattr;
	}
	/* Store valid attribute.
	   str[1] is attributes id constant, str[2] attribute flag. */

	if (P_A_FirstAttr <= str[1] && str[1] <= P_A_LastAttr) {
	    if (!state->values[str[1] & 0xFF])
		state->values[str[1] & 0xFF] = strdup((const char *)str + 2);
	  if (debug)
	    type(NULL,0,NULL,"     accepted!");
	} else {
	  if (debug)
	    type(NULL,0,NULL,"   Unknown attribute, number: %d", str[1]);
	}

    nextattr:

	/* If this wasn't the P_A_MESSAGE, we drop possibly
	   existing message here.. */
	if (str[1] != P_A_MESSAGE) {
	  if (msgstr) free(msgstr);
	  msgstr = NULL;
	}

	rlen -= str[0];
	str  += str[0];

	/* If all requests are done, exit. */
	if (!state->request) {
	  if (debug)
	    type(NULL,0,NULL," Every request found. Finishing search.");
	  break;
	}

    }				/* End of while. */

    /* Free memory from attribute list. Allocated in dbquery. */
    if (str_base)
	free(str_base);

    if (msgstr) free(msgstr);

    return 0;
}


/* Return 0, when found something */
static int checkaddr(state, pbuf)
     struct policystate *state;
     const unsigned char *pbuf;
{
    int result, count, countmax;
    int maxrecursions;
    struct policytest *rel = state->PT;

    maxrecursions = 5;

    if (pbuf[1] == P_K_DOMAIN) {
	if (debug)
	  type(NULL,0,NULL," checkaddr(): domain of '%s'",pbuf+2);
	result = resolveattributes(rel, maxrecursions, state, pbuf, 1);
	if (debug) {
	  type(NULL,0,NULL," Results: %s", showresults(state));
	}
	return (result);
    }
    if (pbuf[1] == P_K_USER) {
	if (debug)
	  type(NULL,0,NULL," checkaddr(): user of '%s'",pbuf+2);
	result = resolveattributes(rel, maxrecursions, state, pbuf, 1);
	if (debug) {
	  type(NULL,0,NULL," Results: %s", showresults(state));
	}
	return (result);
    } else if (pbuf[1] == P_K_IPv4)
	countmax = 32;
    else
	countmax = 128;

    result = 1;
    count = 0;

    while (result != 0 && count <= countmax) {

	count++;
	/* Search database */
	result = resolveattributes(rel, maxrecursions, state, pbuf, 1);
	if (result == 0)	/* Found. */
	    break;

	mask_ip_bits((u_char*)&pbuf[2], countmax - count, countmax);

	if (pbuf[1] == P_K_IPv4)
	    ((char*)pbuf)[6] = 32 - count;	/* Width */
#if defined(AF_INET6) && defined(INET6)
	else			/* AF_INET6 */
	  ((char*)pbuf)[18] = 128 - count;
#endif
    }

    
#if defined(AF_INET6) && defined(INET6)
    /* Umm.. looked for IPv6 address ?  And nothing found ?
       Try then to look for the wild-card [0.0.0.0]/0 entry. */
    if (result != 0 && pbuf[1] == P_K_IPv6) {
      memset((char*)pbuf,0,6);
      ((char*)pbuf)[0] = 7;
      ((char*)pbuf)[1] = P_K_IPv4;
      ((char*)pbuf)[6] = 0;
      /* Search database */
      result = resolveattributes(rel, maxrecursions, state, pbuf, 1);
    }
#endif

    if (result != 0) {
      if (debug)
	type(NULL,0,NULL," Address not found.");
      return -1;
    } else
      if (debug) {
	type(NULL,0,NULL," Results:  %s", showresults(state));
      }
    return 0;
}


static int _addrtest_ __((struct policystate *state, const unsigned char *pbuf, int sourceaddr));

static int _addrtest_(state, pbuf, sourceaddr)
     struct policystate *state;
     const unsigned char *pbuf;
     int sourceaddr;
{
    u_char ipaddr[16];
    int ipaf = pbuf[1];
    int myaddress, lcldom;
    Usockaddr saddr;

    /* Prepare for automatic match of the address */

    memset(&saddr, 0, sizeof(saddr));

    if (pbuf[1] == P_K_IPv4) {
      memcpy(ipaddr, pbuf+2, 4);
      memcpy(& saddr.v4.sin_addr, pbuf+2, 4);
      saddr.v4.sin_family = AF_INET;
    }
    if (pbuf[1] == P_K_IPv6) {
      memcpy(ipaddr, pbuf+2, 16);
#if defined(AF_INET6) && defined(INET6)
      memcpy(& saddr.v6.sin6_addr, pbuf+2, 4);
      saddr.v6.sin6_family = AF_INET6;
#endif
    }

    lcldom = (state->request & (1 << P_A_LocalDomain));
    myaddress = matchmyaddress(&saddr);

    if (debug)
      type(NULL,0,NULL," policytestaddr: lcldom/myaddress=%d/%d",lcldom,myaddress);

    /* state->request initialization !! */

    if (sourceaddr)
      state->request = ( 1 << P_A_REJECTNET         |
			 1 << P_A_FREEZENET         |
			 1 << P_A_RELAYCUSTNET      |
			 1 << P_A_InboundSizeLimit  |
			 1 << P_A_OutboundSizeLimit |
			 1 << P_A_FullTrustNet      |
			 1 << P_A_TrustRecipients   |
#ifdef HAVE_WHOSON_H
			 1 << P_A_TrustWhosOn       |
#endif
			 1 << P_A_Filtering         |
			 1 << P_A_RateLimitMsgs     |
			 1 << P_A_MaxSameIpSource    );
    if (!myaddress)
      state->request |= ( 1 << P_A_TestDnsRBL       |
			  1 << P_A_RcptDnsRBL       |
			  1 << P_A_CheckSPF          );

    state->maxinsize  = -1;
    state->maxoutsize = -1;

    if (checkaddr(state, pbuf) != 0)
      return 0; /* Nothing found */


    if (state->values[P_A_RateLimitMsgs]) {
      if (state->ratelimitmsgsvalue)	free (state->ratelimitmsgsvalue);
      state->ratelimitmsgsvalue = strdup(state->values[P_A_RateLimitMsgs]);
      PICK_PA_MSG(P_A_RateLimitMsgs);
    }

    if (myaddress && lcldom) {

      if (state->values[P_A_LocalDomain]) free(state->values[P_A_LocalDomain]);
      state->values[P_A_LocalDomain] = strdup("+");
      if (state->values[P_A_RELAYTARGET]) free(state->values[P_A_RELAYTARGET]);
      state->values[P_A_RELAYTARGET] = strdup("+");
      if (state->values[P_A_TestDnsRBL]) free(state->values[P_A_TestDnsRBL]);
      state->values[P_A_TestDnsRBL] = NULL;
      if (state->values[P_A_RcptDnsRBL]) free(state->values[P_A_RcptDnsRBL]);
      state->values[P_A_RcptDnsRBL] = NULL;

      if (state->values[P_A_Filtering]) {
	if (debug)
	  type(NULL,0,NULL," policytestaddr: 'filter %s' found",
		 state->values[P_A_Filtering]);
	if (valueeq(state->values[P_A_Filtering], "+")) {
	  state->content_filter = 1;
	} else {
	  state->content_filter = 0;
	}
      }

      if (debug)
	type(NULL,0,NULL," Results:  %s", showresults(state));

      return 0;
    }

    if (!sourceaddr)
      goto just_rbl_checks;


#if 0
/* if (IP address of SMTP client has 'rejectnet +' attribute) then
    any further conversation refused
    [state->always_reject = 1; return -1;]
    ...
   if (IP address of SMTP client has 'freezenet +' attribute) then
    we present happy face, but always put the messages into a freezer..
    [state->always_freeze = 1; return -1;]
   if (IP address of SMTP client has 'relaycustnet +' attribute) then
    sender accepted, recipients not checked
    [state->always_accept = 1; return 0;]
    ...
   Except that:
   if (HELO-name of SMTP client has 'rejectnet +' attribute) then
    any further conversation refused
    [state->always_reject = 1; return -1;]
   else if (sender's domain has 'rejectsource +' attribute) then
    sender rejected, any further conversation refused
    [state->sender_reject = 1; return -1;]
 */
#endif

    if (state->message != NULL)
      free(state->message);
    state->message = NULL;

    if (valueeq(state->values[P_A_REJECTNET], "+")) {
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'rejectnet +' found");
      PICK_PA_MSG(P_A_REJECTNET);
      if (state->message == NULL)
	state->message = strdup("Your network address is blackholed in our static tables");
      state->always_reject = 1;
      return -1;
    }
    if (valueeq(state->values[P_A_FREEZENET], "+")) {
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'freezenet +' found");
      PICK_PA_MSG(P_A_FREEZENET);
      if (state->message == NULL)
	state->message = strdup("Your network address is blackholed in our static tables");
      state->always_freeze = 1;
      return  1;
    }
    if (valueeq(state->values[P_A_TrustRecipients], "+")) {
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'trustrecipients +' found");
      state->trust_recipients = 1;
      PICK_PA_MSG(P_A_TrustRecipients);
    }
    if (valueeq(state->values[P_A_FullTrustNet], "+")) {
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'fulltrustnet +' found");
      state->full_trust = 1;
      PICK_PA_MSG(P_A_FullTrustNet);
    }
    if (/* !state->implied_submission_mode && */
	valueeq(state->values[P_A_RELAYCUSTNET], "+")) {
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'relaycustnet +' found");
      state->always_accept = 1;
      PICK_PA_MSG(P_A_RELAYCUSTNET);
    }

#ifdef HAVE_WHOSON_H
    if (valueeq(state->values[P_A_TrustWhosOn], "+")) {
      if (state->valid_whoson){
	state->trust_recipients = 1;
       state->whoson_at_ip = 1;
        if (debug) 
          type(NULL,0,NULL," policytestaddr: 'trust-whoson +' found at IP address.  (named or _default_ipaddr?)  Trust-Recipients granted.");
        PICK_PA_MSG(P_A_TrustRecipients);
      }
    } else if (valueeq(state->values[P_A_TrustWhosOn], "-")) {
      if (state->valid_whoson){
	state->valid_whoson = 0;
        if (debug) 
          type(NULL,0,NULL," policytestaddr: 'valid whoson query but trust-whoson -' found at IP address (named or _default_ipaddr?),   Valid-Whoson revoked.");
      }
    }

#endif

    if (state->values[P_A_Filtering]) {
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'filter %s' found",
	       state->values[P_A_Filtering]);
      if (valueeq(state->values[P_A_Filtering], "+")) {
	state->content_filter = 1;
      } else {
	state->content_filter = 0;
      }
    }

    if (state->trust_recipients || state->full_trust || state->always_accept)
      return 0;

 just_rbl_checks:;

    if (state->values[P_A_Filtering]) {
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'filter %s' found",
	       state->values[P_A_Filtering]);
      if (valueeq(state->values[P_A_Filtering], "+")) {
	state->content_filter = 1;
      } else {
	state->content_filter = 0;
      }
    }

    if (valueeq(state->values[P_A_CheckSPF], "+")) {
#ifdef Z_CHECK_SPF_DATA
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'spf +' found");
      initialize_spf(state);
#else
      type(NULL,0,NULL," compiled without SPF support, 'spf +' ignored");
#endif
    }

    if (state->values[P_A_TestDnsRBL] &&
	!valueeq(state->values[P_A_TestDnsRBL], "-")) {
      int rc;
      time_t then;
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'test-dns-rbl %s' found;",
	       state->values[P_A_TestDnsRBL]);
      time(&then);
      rc = rbl_dns_test(state, ipaf, ipaddr, state->values[P_A_TestDnsRBL], &state->message);
      time(&now);
      if ((now - then) > 30)
	type(NULL,0,NULL,"RBL_DNS_TEST() TOOK %d SECONDS!",
	     (int)(now - then));

      if (rc < 0 && !state->message) {
	PICK_PA_MSG(P_A_TestDnsRBL);
      }

      if (debug)
	type(NULL,0,NULL,"  rc=%d; msg='%s'",
	     rc, state->message ? state->message : "<nil>");

      return rc;
    }

    /* bag = Andrey Blochintsev <bag@iptelecom.net.ua>  */
    /* bag + */
    if (state->values[P_A_RcptDnsRBL] &&
	state->values[P_A_RcptDnsRBL][0] == '_') {
      int rc = 1;
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'rcpt-dns-rbl %s' found;",
	       state->values[P_A_RcptDnsRBL]);
      if (state->values[P_A_RcptDnsRBL][1] != '+') {
      	if (state->rblmsg != NULL)
	  free(state->rblmsg);
	state->rblmsg = strdup(state->values[P_A_RcptDnsRBL] + 1);
	rc = 0;
      }
      /* if (!state->message){ PICK_PA_MSG(P_A_RcptDnsRBL); } */
      if (debug)
	type(NULL,0,NULL,"  rc=%d", rc);
      return 0; /* We report error LATER */

    }
    /* bag - */

    if (state->values[P_A_RcptDnsRBL] &&
	!valueeq(state->values[P_A_RcptDnsRBL], "-")) {
      int rc;
      time_t then;
      if (debug)
	type(NULL,0,NULL," policytestaddr: 'rcpt-dns-rbl %s' found;",
	       state->values[P_A_RcptDnsRBL]);
      time(&then);
      rc = rbl_dns_test(state, ipaf, ipaddr, state->values[P_A_RcptDnsRBL], &state->rblmsg);
      time(&now);
      if ((now - then) > 30)
	type(NULL,0,NULL,"RBL_DNS_TEST() TOOK %d SECONDS!",
	     (int)(now - then));

      if (rc <0 &&  !state->rblmsg) {
	if (state->messages[P_A_RcptDnsRBL]) {
	  state->rblmsg = strdup(state->messages[P_A_RcptDnsRBL]);
	  state->messages[P_A_RcptDnsRBL] = NULL;
	} else {
	  state->rblmsg = strdup("You are on our reject-IP-address -list, GO AWAY!");
	}
      }

      if (debug)
	type(NULL, 0, NULL, "rcpt-dns-rbl test yields: rc=%d rblmsg='%s'", rc,
	     state->rblmsg ? state->rblmsg : "<none>");

      /* if (!state->message){ PICK_PA_MSG(P_A_RcptDnsRBL); } */
      /* if (debug) type(NULL,0,NULL,"  rc=%d", rc); */
      return 0; /* We report error LATER */
    }
    return 0;
}

int policytestaddr(state, what, raddr)
     struct policystate *state;
     PolicyTest what;
     Usockaddr *raddr;
{
    unsigned char pbuf[64]; /* Not THAT much space needed.. */
    int rc;

    struct sockaddr_in *si4;
#if defined(AF_INET6) && defined(INET6)
    struct sockaddr_in6 *si6;
#endif


    if (what != POLICY_SOURCEADDR)
      abort();		/* Urgle..! Code mismatch! */

    if (state->PT == NULL)
      return 0;

    /* Find address match -- IPv4 mapped into IPv6 space too! */

    state->message = NULL; /* This is early initial clearing */

    if (raddr->v4.sin_family == 0) {
      state->full_trust = 1;
      return 0; /* Interactive testing... */
    }

    if (raddr->v4.sin_family == AF_INET) {
      si4 = & (raddr->v4);
      pbuf[0] = 7;
      pbuf[1] = P_K_IPv4;
      memcpy(&pbuf[2], (char *) &si4->sin_addr.s_addr, 4);
      pbuf[6] = 32;		/* 32 bits */
    } else
#if defined(AF_INET6) && defined(INET6)
    if (raddr->v6.sin6_family == AF_INET6) {
      si6 = & (raddr->v6);
      if (memcmp((void *)&si6->sin6_addr, zv4mapprefix, 12) == 0) {
	/* This is IPv4 address mapped into IPv6 */
	pbuf[0] = 7;
	pbuf[1] = P_K_IPv4;
	memcpy(pbuf+2, ((char *) &si6->sin6_addr) + 12, 4);
	pbuf[6] = 32;			/*  32 bits */
      } else {
	pbuf[0] = 19;
	pbuf[1] = P_K_IPv6;
	memcpy(pbuf+2, ((char *) &si6->sin6_addr), 16);
	pbuf[18] = 128;		/* 128 bits */
      }
    } else
#endif
    {
      type(NULL,0,NULL,"Unknown address format; sa_family = %d",
	   raddr->v4.sin_family);
      return -2;
    }

#if defined(AF_INET6) && defined(INET6)
    if (pbuf[1] == P_K_IPv6) {
      char *s;
      unsigned char *p;
      int i;

      strcpy(state->ratelabelbuf, "6:");
      p = pbuf+2;
      s = state->ratelabelbuf+2;
      for (i = 0; i < 16; ++i) {
	sprintf(s, "%02x", *p);
	s += 2; ++p;
      }
    } else
#endif
      {
	char *s;
	unsigned char *p;
	int i;

	strcpy(state->ratelabelbuf, "4:");
	p = pbuf+2;
	s = state->ratelabelbuf+2;
	for (i = 0; i < 4; ++i) {
	  sprintf(s, "%02x", *p);
	  s += 2; ++p;
	}
      }

    state->request = 0;
    state->content_filter = -1;

    rc = _addrtest_(state, pbuf, 1);

#if defined(HAVE_SPF_ALT_SPF_H) || defined(HAVE_SPF2_SPF_H)
    if (state->check_spf) {
      if (debug) {
	char aaa[32];
	inet_ntop(raddr->v4.sin_family,&raddr->v4.sin_addr,aaa,sizeof(aaa));
	if (debug) type(NULL,0,NULL,"doing SPF_set_ipv4(%s)",aaa);
      }
#if defined(AF_INET6) && defined(INET6)
      if (raddr->v6.sin6_family == AF_INET6) {
	if (SPF_set_ipv6(state->spfcid, raddr->v6.sin6_addr)) {
	  type(NULL,0,NULL,"SPF_set_ipv6() failed");
	  state->check_spf=0;
	}
      } else
#endif
      {
	if (SPF_set_ipv4(state->spfcid, raddr->v4.sin_addr)) {
	  type(NULL,0,NULL,"SPF_set_ipv4() failed");
	  state->check_spf=0;
	}
      }
    }
#endif /* HAVE_SPF_ALT_SPF_H || HAVE_SPF2_SPF_H */

    if (debug) fflush(stdout);
    return rc;
}

static int check_domain(state, input, inlen)
     struct policystate *state;
     const unsigned char *input;
     int inlen;
{
    unsigned char *ptr, *ptr2, pbuf[256];
    int addr_len, i, plen, result;


#if 0
    /* Get address after @ */
    ptr = strchr((const char *)input, '@');
    if (ptr == NULL) {
	printf("Invalid address. @ not found!\n");
	exit(0);
    }
    ptr++;
    addr_len = inlen - (ptr - input);
#else
    ptr = (unsigned char*)input;
    addr_len = inlen;
#endif

    /* Convert to lower case. */
    if (addr_len > sizeof(pbuf)-3)
	addr_len = sizeof(pbuf)-3;
    memcpy(pbuf+2, ptr, addr_len);
    pbuf[2+addr_len] = 0;
    strlower((char*)pbuf+2);

    if (pbuf[2] == '[') {
      /* IP address literal ??? */
      if (strncmp((const char*)pbuf+2+1,"ipv6",4)==0) {
#if defined(AF_INET6) && defined(INET6)
	char *s = strchr((const char *)pbuf+3,']');
	if (s) *s = 0;
	if (inet_pton(AF_INET6, (const char*)pbuf+3+5, pbuf+2) < 1) {
	  /* XX: Duh ?  Our input is syntax checked, so
	     this ERROR should not happen.. */
	}
	pbuf[0] = 19;
	pbuf[1] = P_K_IPv6;
	pbuf[18] = 128;
#else
	/* XXX: Duh ??? IPv6 not supported, how to report errs ?? */
#endif
      } else {
	char *s = strchr((const char *)pbuf+3,']');
	if (s) *s = 0;
	if (inet_pton(AF_INET, (const char *)pbuf+3, (u_char *)pbuf+2) < 1) {
	  /* XX: Duh ?  Our input is syntax checked, so
	     this ERROR should not happen.. */
	}

	pbuf[0] = 7;
	pbuf[1] = P_K_IPv4;
	pbuf[6] = 32;
      }
      return _addrtest_(state,pbuf, 0);
    }

    plen = addr_len;
    /* '\0' not included in inlen... */
    plen += 1 + 2;

    pbuf[0] = plen;
    pbuf[1] = P_K_DOMAIN;

    result = 1;

    while (result != 0) {
	if (debug)
	  type(NULL,0,NULL," DEBUG: %s", showkey(pbuf));
	result = checkaddr(state, pbuf);

	if (result == 0) /* Found! */
	  return 0;

	if (pbuf[2] != '.') {
	    /* Put '.' in the beginning */
	    for (i = pbuf[0]; i >= 2; --i) {
		pbuf[i + 1] = pbuf[i];
	    }
	    pbuf[2] = '.';
	    pbuf[0] += 1;
	} else {
	    /* Test with shorter address. */
	    ptr = &pbuf[3];
	    while (*ptr != 0 && *ptr != '.')
		ptr++;
	    if (*ptr == '\0') {
		/* Quit the loop if everything is examined. */
		if (pbuf[2] == '.' && pbuf[3] == '\0')
		    break;
		pbuf[2] = '.';
		pbuf[3] = '\0';
	    } else {
		ptr++;
		ptr2 = &pbuf[3];
		while (*ptr != '\0') {
		    *ptr2++ = *ptr++;
		}
		*ptr2++ = *ptr++;
	    }
	    pbuf[0] = strlen((char*)&pbuf[2]) + 1 + 2;
	}
    }
    return 0; /* Nothing found */
}

static const unsigned char * find_nonqchr __((const unsigned char *, int, int));
static const unsigned char *
find_nonqchr(input, chr, inlen)
     const unsigned char *input;
     int chr, inlen;
{
  int quote = 0;
  /* Find first unquoted ``chr'' character, and return a pointer to it */
  for (; inlen > 0; --inlen,++input) {
    if (*input == '"')
      quote = !quote;
    if (*input == '\\') {
      --inlen; ++input;
      continue;
    }
    if (*input == chr && !quote)
      return input;
  }
  return NULL;
}

/* Return 0, when found something */
static int check_user(state, input, inlen)
     struct policystate *state;
     const unsigned char *input;
     int inlen;
{
    unsigned char pbuf[512];
    const unsigned char *at;
    int result;

    if (inlen > (sizeof(pbuf) - 3))
      inlen = sizeof(pbuf) - 3;

    /* Store the MAIL FROM:<user@domain> into a temporary buffer, and
       lowercasify it   */
    memcpy(pbuf+2, input, inlen);
    pbuf[2+inlen] = 0;
    strlower((char*)pbuf + 2);

    at = find_nonqchr(pbuf + 2, '@', inlen);
    if (!at) return 0;

    pbuf[inlen + 2] = '\0';
    pbuf[0] = inlen + 1 + 2;
    pbuf[1] = P_K_USER;

    result = checkaddr(state, pbuf);
    if (result == 0) /* Found! */
      return result;

    /* 'user@' */
    inlen = (at+1 - pbuf) - 2;
    pbuf[inlen + 2] = '\0';
    pbuf[0] = inlen + 1 + 2;
    pbuf[1] = P_K_USER;

    result = checkaddr(state, pbuf);
    return result;
}


static int pt_heloname __((struct policystate *, const unsigned char *, const int));

static int pt_mailfrom __((struct policystate *, const unsigned char *, const int));

static int pt_rcptto __((struct policystate *, const unsigned char *, const int));

static int pt_rcptpostmaster __((struct policystate *, const unsigned char *, const int));

static int pt_heloname(state, str, len)
     struct policystate *state;
     const unsigned char *str;
     const int len;
{
#ifdef DO_PERL_EMBED
    int rc;
#endif

    if (state->always_reject)
	return -1;
    if (state->always_freeze)
	return 1;
    if (state->always_accept)
	return 0;
    if (state->full_trust || state->authuser)
	return 0;

    /*
     * This is somewhat controversial.
     * This exists solely to allow simplification of
     * smtpserver.conf  file by having the HELO/EHLO
     * strings to be rejected stored in the policy
     * database.
     *
     * In Sep-2001 it became apparent that very least
     * there is no point in analyzing '[...]' numeric
     * HELO parameter contained address data.
     *
     * Current code will only look for the input string
     * in the database (by domain lookup protocol), and
     * react on it by slamming the door shut (if any).
     *
     */

#ifdef Z_CHECK_SPF_DATA
    if (state->check_spf) {
      if (debug) type(NULL,0,NULL,"doing SPF_set_helo_dom(\"%s\")",str);
      if (SPF_set_helo_dom(state->spfcid, (const char *)str)) {
	  type(NULL,0,NULL,"SPF_set_helo_dom() failed");
	  state->check_spf=0;
      }
    }
#endif

#ifdef DO_PERL_EMBED
    if (use_perlhook && ZSMTP_hook_univ(ZSMTP_HOOK_HELO, state, str, len, &rc))
      return rc;
#endif

    if (*str != '[') { /* Don't test address literals! */

      /* state->request initialization !! */
      state->request = ( 1 << P_A_REJECTNET    |
			 1 << P_A_FREEZENET  );

      check_domain(state, str, len);

/*
   # if (name of SMTP client has 'rejectnet +' attribute) then
   #    any further conversation refused
   #      [state->always_reject = 1; return -1;]
 */
      if (valueeq(state->values[P_A_REJECTNET], "+")) {
	state->always_reject = 1;
	PICK_PA_MSG(P_A_REJECTNET);
	return -1;
      }
      if (valueeq(state->values[P_A_FREEZENET], "+")) {
	state->always_freeze = 1;
	PICK_PA_MSG(P_A_FREEZENET);
	return  1;
      }

    }

    return 0;
}

static int pt_sourcedomain(state, str, len)
     struct policystate *state;
     const unsigned char *str;
     const int len;
{
    if (state->always_reject)
	return -1;
    if (state->always_freeze)
	return 1;
    if (state->full_trust || state->authuser)
	return 0;

    /* state->request initialization !! */
    state->request = ( 1 << P_A_REJECTNET    |
		       1 << P_A_FREEZENET    |
		       1 << P_A_RELAYCUSTNET |
		       1 << P_A_InboundSizeLimit  |
		       1 << P_A_OutboundSizeLimit  );
    state->request |= ( 1 << P_A_RcptDnsRBL );	/* bag */

    check_domain(state, str, len);

/*
   # if (name of SMTP client has 'rejectnet +' attribute) then
   #    any further conversation refused
   #      [state->always_reject = 1; return -1;]
 */
    if (valueeq(state->values[P_A_REJECTNET], "+")) {
	state->always_reject = 1;
	PICK_PA_MSG(P_A_REJECTNET);
	return -1;
    }
    if (valueeq(state->values[P_A_FREEZENET], "+")) {
	state->always_freeze = 1;
	PICK_PA_MSG(P_A_FREEZENET);
	return  1;
    }

    if (state->always_accept)
	return 0;

    if (/* !state->implied_submission_mode && */
	valueeq(state->values[P_A_RELAYCUSTNET], "+")) {
      if (debug)
	type(NULL,0,NULL," pt_sourceaddr: 'relaycustnet +' found");
      state->always_accept = 1;
      PICK_PA_MSG(P_A_RELAYCUSTNET);
      return  0;
    }
    if (valueeq(state->values[P_A_FullTrustNet], "+")) {
      if (debug)
	type(NULL,0,NULL," pt_sourceaddr: 'fulltrustnet +' found");
      state->full_trust = 1;
      PICK_PA_MSG(P_A_FullTrustNet);
      return  0;
    }
    /* bag + */
    if (state->rblmsg == NULL &&	/* only if no rbl_message before (from lookup by net) */
	state->values[P_A_RcptDnsRBL] &&
	state->values[P_A_RcptDnsRBL][0] == '_') {
      if (debug)
	type(NULL,0,NULL," pt_sourceaddr: 'rcpt-dns-rbl %s' found;",
	       state->values[P_A_RcptDnsRBL]);
      if (state->values[P_A_RcptDnsRBL][1] != '+') {
	state->rblmsg = strdup(state->values[P_A_RcptDnsRBL] + 1);
      }
      free(state->values[P_A_RcptDnsRBL]);
      return 0; /* We report error LATER */

    }
    /* bag - */
    return 0;
}

static int pt_mailfrom(state, str, len)
     struct policystate *state;
     const unsigned char *str;
     const int len;
{
    const unsigned char *at;
    int requestmask = 0;
    int rc;

    state->sender_reject = 0;
    state->sender_freeze = 0;
    state->sender_norelay = 0;

    /*
     * This is a Whoson HACK
     *   If a previous MAIL FROM in this SMTP session
     *   found a trust-whoson match, state->trust-recipients
     *   was granted.  Reset it now, in case the policy
     *   configuration specifies per domain whoson trust
     *  
     * If we do not reset, all further recipients would
     *   be accepted even if new from addresses did not have
     *   a trust whoson match
     */
#ifdef HAVE_WHOSON_H
     if (state->valid_whoson && state->trust_recipients &&
       (! state->whoson_at_ip) &&
       (! valueeq(state->values[P_A_TrustRecipients], "+"))){
       state->trust_recipients = 0;
       if (debug)
         type(NULL,0,NULL," pt_mailfrom: resetting whoson forged: state->trust_recipients");
     }
#endif


#ifdef Z_CHECK_SPF_DATA
    if (state->check_spf) {
      char *nstr=strdup((const char *)str);
      nstr[len]='\0';
      if (debug) type(NULL,0,NULL,"doing SPF_set_env_from(\"%s\")",nstr);
      if (SPF_set_env_from(state->spfcid, nstr)) {
	  type(NULL,0,NULL,"SPF_set_env_from(\"%s\") failed",nstr);
	  state->check_spf=0;
      }
      free(nstr);
    }
#endif

    if (state->always_reject)
	return -1;
    if (state->always_freeze)
	return 1;
    if (state->full_trust)
	return 0;

#ifdef DO_PERL_EMBED
    if (use_perlhook &&
	ZSMTP_hook_univ(ZSMTP_HOOK_MAILFROM, state, str, len, &rc))
      return rc;
#endif

    if (len > 0) { /* Non-box address.. */

      /* state->request initialization !! */
      state->request = ( 1 << P_A_REJECTSOURCE |
#ifdef HAVE_WHOSON_H
			 (state->valid_whoson ? 1:0) << P_A_TrustWhosOn  |
#endif
			 1 << P_A_FREEZESOURCE   );

      /* XX: How about  <@foo:user@domain> ??? */
      /* XX: With IGNORING RFC-821-source-route "@foo:" we
	 don't have problems here */

      /* Check source user */
      if (check_user(state, str, len) == 0) {
	if (valueeq(state->values[P_A_FREEZESOURCE], "+")) {
	  if (debug)
	    type(NULL,0,NULL," mailfrom: 'freezesource +'");
	  state->sender_freeze = 1;
	  PICK_PA_MSG(P_A_FREEZESOURCE);
	  return 1;
	}
	if (state->values[P_A_FREEZESOURCE])
	  requestmask |= 1 << P_A_FREEZESOURCE;
	
	if (valueeq(state->values[P_A_REJECTSOURCE], "+")) {
	  if (debug)
	    type(NULL,0,NULL," mailfrom: 'rejectsource +'");
	  state->sender_reject = 1;
	  PICK_PA_MSG(P_A_REJECTSOURCE);
	  return -1;
	}
	if (state->values[P_A_REJECTSOURCE])
	  requestmask |= 1 << P_A_REJECTSOURCE;
      }

      state->request = ( 1 << P_A_REJECTSOURCE  |
			 1 << P_A_FREEZESOURCE  |
#if 0
			 1 << P_A_RELAYCUSTOMER |
#endif
#ifdef HAVE_WHOSON_H
			 (state->valid_whoson ?1:0) << P_A_TrustWhosOn  |
#endif
			 1 << P_A_SENDERNoRelay |
			 1 << P_A_SENDERokWithDNS ) & (~ requestmask);

      at = find_nonqchr(str, '@', len);
      if (at != NULL) {
	/* @[1.2.3.4] ?? */
	if (check_domain(state, at+1, len - (1 + at - str)) != 0)
	  return -1;
      } else {
	/* Doh ??  Not  <user@domain> ??? */
	return -1;
      }

    } else { /* The case of: "MAIL FROM:<>" */

      state->request = ( 1 << P_A_REJECTSOURCE  |
			 1 << P_A_FREEZESOURCE  |
#if 0
			 1 << P_A_RELAYCUSTOMER |
#endif
			 1 << P_A_SENDERNoRelay |
			 1 << P_A_SENDERokWithDNS ) & (~ requestmask);

      if (check_domain(state, (const unsigned char *)".", 1) != 0)
	  return -1;
      at = str;
    }


    if ((len > 0) && valueeq(state->values[P_A_SENDERNoRelay], "+")) {
      if (debug)
	type(NULL,0,NULL," mailfrom: 'sendernorelay +'");
      state->sender_norelay = 1;
      PICK_PA_MSG(P_A_SENDERNoRelay);
    }

    if (debug)
      type(NULL,0,NULL,"mailfrom; always_accept=%d ratelimitmsgsvalue='%s'",
	   state->always_accept,
	   (state->ratelimitmsgsvalue ? state->ratelimitmsgsvalue : "<nil>"));

    if (state->always_accept && state->ratelimitmsgsvalue) {
      /* If we are in 'alwaysaccept' mode, which is true for IP-acl:s,
	 then we check to see rate-limits */

      int count, count2 = 0;
      int limitval1, limitval2 = 0;

      if (debug)
	type(NULL,0,NULL,"Checking 'RateLimitMsgs %s' attribute",
	     state->ratelimitmsgsvalue);

      count = sscanf(state->ratelimitmsgsvalue, "%d,%d", &limitval1, &limitval2);
      if (count == 1 || count == 2) {
	/* Valid numeric value had.. */

	int rc;

	if (state->authuser) {
	  limitval1 *= 10; /* raise the limit considerably for
			      authenticated user. */
	  limitval2 *= 10; /* raise the limit considerably for
			      authenticated user. */
	}

	rc = call_rate_counter(state, 0, POLICY_MAILFROM,
			       &count, &count2);

	/* Non-zero value means that counter was not reachable, or
	   that there was no data. */

	if (rc == 0) {
	  /* Got some rate limit data back,  now USE IT ! */
	  if (limitval1 < 0 && count >= -limitval1) {
	    PICK_PA_MSG(P_A_RateLimitMsgs);
	    rc = -1;  /* Hard, e.g. 500-series */
	  } else if (limitval1 > 0 && count >= limitval1) {
	    PICK_PA_MSG(P_A_RateLimitMsgs);
	    rc = -100; /* Soft, e.g. 400-series */
	  } else if (limitval2 < 0 && count >= -limitval2) {
	    PICK_PA_MSG(P_A_RateLimitMsgs);
	    rc = -1;  /* Hard, e.g. 500-series */
	  } else if (limitval2 > 0 && count >= limitval2) {
	    PICK_PA_MSG(P_A_RateLimitMsgs);
	    rc = -100; /* Soft, e.g. 400-series */
	  }

	  if ((rc != 0)  && (! state->message))
	    state->message = strdup("You are sending too much mail/rcpts per time interval.  Try again latter.");
	  if (rc != 0) {
	    /* register the excess! */
	    call_rate_counter(state, 1, POLICY_EXCESS, &count, NULL);
	  }
	  /* Reject here, if something rejects, otherwise pass on.. */
	  if (rc != 0)
	    return rc;
	}
      }
    }

    if (valueeq(state->values[P_A_REJECTSOURCE], "+")) {
	if (debug)
	  type(NULL,0,NULL," mailfrom: 'rejectsource +'");
	state->sender_reject = 1;
	PICK_PA_MSG(P_A_REJECTSOURCE);
	return -1;
    }

    if (valueeq(state->values[P_A_FREEZESOURCE], "+")) {
	if (debug)
	  type(NULL,0,NULL," mailfrom: 'freezesource +'");
	state->sender_freeze = 1;
	PICK_PA_MSG(P_A_FREEZESOURCE);
	return -1;
    }

#ifdef HAVE_WHOSON_H
    if (state->valid_whoson){
      if (valueeq(state->values[P_A_TrustWhosOn], "+")) {
	state->trust_recipients = 1;
        if (debug) 
          type(NULL,0,NULL," policytestaddr: 'trust-whoson +' found at EMail address.  (named or _default_dot?)  Trust-Recipients granted.");
        PICK_PA_MSG(P_A_TrustRecipients);
      }
    }
#endif



    if ((len > 0)  && (at[1] != '[') && state->values[P_A_SENDERokWithDNS]) {
      /*
       * Reject if not found in DNS (and not an address literal)
       */
      int test_c = state->values[P_A_SENDERokWithDNS][0];
      int rc;
      time_t then;
      time(&then);

      if (debug)
	type(NULL,0,NULL," doing SENDERokWithDNS analysis: '%.*s'",
	     len - (1 + at - str), at + 1);

      rc = sender_dns_verify( state, test_c, (const char *)at+1,
			      len - (1 + at - str) );
      time(&now);
      if ((now - then) > 30)
	type(NULL,0,NULL,"SENDER_DNS_VERIFY() TOOK %d SECONDS!",
	     (int)(now - then));

      if (debug)
	type(NULL,0,NULL," ... returns: %d", rc);
      PICK_PA_MSG(P_A_SENDERokWithDNS);
      if (rc != 0) return rc;
    }

    if (state->authuser) {
      if (debug)
	type(NULL,0,NULL," allow authenticated user");
      return 0;
    }

    if ( state->always_accept ) {
      if (debug)
	type(NULL,0,NULL," allow because of \"always-accept\"");
      return 0;
    }


#ifdef Z_CHECK_SPF_DATA
    rc=0;
    if (state->check_spf) {
      int spf_level;
      SPF_output_t spf_output;

      spf_output = SPF_result(state->spfcid, state->spfdcid);

      if (debug) {
	type(NULL,0,NULL," SPF_result=%d (%s) reason=%d (%s) error=%d (%s)",
	     spf_output.result,
	     SPF_strresult(spf_output.result),
	     spf_output.reason,
	     SPF_strreason(spf_output.reason),
	     spf_output.err,
	     SPF_strerror(spf_output.err));
	type(NULL,0,NULL,"%s",( spf_output.smtp_comment ?
				spf_output.smtp_comment : "<null>") );
      }

      if (state->spf_received_hdr != NULL)
	free(state->spf_received_hdr);
      state->spf_received_hdr = strdup(spf_output.received_spf);

      if (debug)
	type(NULL,0,NULL,"%s", (state->spf_received_hdr ?
				state->spf_received_hdr : "<null>") );

      switch (spf_output.result) {
      case SPF_RESULT_PASS:	spf_level=5; break;
      case SPF_RESULT_UNKNOWN:	spf_level=5; break;
      case SPF_RESULT_ERROR:	spf_level=5; break;
      case SPF_RESULT_NEUTRAL:	spf_level=4; break;
      case SPF_RESULT_NONE:	spf_level=3; break;
      case SPF_RESULT_SOFTFAIL:	spf_level=2; break;
      case SPF_RESULT_FAIL:	spf_level=1; break;
      default:			spf_level=5; break;
      }
      if (debug)
	type(NULL,0,NULL,
	     "rejecting if spf_level(%d) < spf_threshold(%d)",
	     spf_level,spf_threshold);

      if (spf_level < spf_threshold) {
	if (spf_output.smtp_comment) {
	  state->message = strdup(spf_output.smtp_comment);
	} else {
	  PICK_PA_MSG(P_A_CheckSPF);
	}
	rc=-1;
      }
      SPF_free_output(&spf_output);
    }

    /* SPF has said: BOO BOO! */
    if (rc != 0)
      return rc;
#endif

    /* If nobody requested reject so far, do allow... */
    return 0;
}

static int pt_rcptto(state, str, len)
     struct policystate *state;
     const unsigned char *str;
     const int len;
{
    const unsigned char *at;
    int localdom, relayable = 0;
    int loopbreak = 20;
#ifdef DO_PERL_EMBED
    int rc;
#endif

    if (state->always_reject) return -1;
    if (state->sender_reject) return -2;
    if (state->always_freeze) return  1;
    if (state->sender_freeze) return  1;
    if (state->full_trust)    return  0;
    if (state->authuser)      return  0;
    if (state->trust_recipients) return 0;

#ifdef DO_PERL_EMBED
    if (use_perlhook &&
	ZSMTP_hook_univ(ZSMTP_HOOK_RCPTTO, state, str, len, &rc))
      return rc;
#endif

    /* rcptfreeze even for 'rcpt-nocheck' ? */

    /* state->request initialization !! */
    state->request = ( 1 << P_A_RELAYTARGET     |
		       1 << P_A_ACCEPTbutFREEZE |
		       1 << P_A_TestRcptDnsRBL  |
		       1 << P_A_LocalDomain );

    /* Test first the full address */
    if (check_user(state, str, len) == 0) {
      if (valueeq(state->values[P_A_RELAYTARGET], "+")) {
	PICK_PA_MSG(P_A_RELAYTARGET);
	return  0;
      }
      if (valueeq(state->values[P_A_RELAYTARGET], "-")) {
	PICK_PA_MSG(P_A_RELAYTARGET);
	return -1;
      }
      if (valueeq(state->values[P_A_ACCEPTbutFREEZE], "+")) {
	state->sender_freeze = 1;
	PICK_PA_MSG(P_A_ACCEPTbutFREEZE);
	return  1;
      }
      if (valueeq(state->values[P_A_TestRcptDnsRBL], "+")) {

	type(NULL, 0, NULL, "test-rcpt-dns-rbl test; rblmsg='%s'",
	     state->rblmsg ? state->rblmsg : "<none>");

	if (state->rblmsg != NULL) {
	  /* Now this is cute... the source address had RBL entry,
	     and the recipient domain had a request to honour the
	     RBL data. */
	  if (state->message != NULL) free(state->message);
	  state->message = strdup(state->rblmsg);
	  if (debug)
	    type(NULL,0,NULL," ... TestRcptDnsRBL has a message: '%s'",
		   state->rblmsg);
	  return -1;
	}
      }
    }

    /* state->request initialization !! */
    state->request = ( 1 << P_A_RELAYTARGET     |
		       1 << P_A_ACCEPTbutFREEZE |
		       1 << P_A_ACCEPTifMX      |
		       1 << P_A_ACCEPTifDNS     |
		       1 << P_A_TestRcptDnsRBL  |
		       1 << P_A_LocalDomain );

    at = find_nonqchr(str, '@', len);
    if (at != NULL) {
      if (check_domain(state, at+1, len - (1 + at - str)) != 0) {
	type(NULL,0,NULL,"rcptto checkdomain fails; -1");
	return -1;
      }
    } else {
      if (state->always_accept) {
	return 0;
      }

      /* Doh ??  Not  <user@domain> ??? */
      return -1;
    }

/*
   # else if (recipient's domain has 'relaytarget +' attribute) then
   #    recipient accepted
   #      [return  0;]
   # else if (recipient's domain has 'freeze +' attribute) then
   #    the MESSAGE is accepted into a freezer..
   #      [state->sender_freeze = 1; return -1;]
   # else
   #    this recipient refused
   #      [return -1;]
 */

 process_local_domain:;

    while ((localdom = valueeq(state->values[P_A_LocalDomain], "+")) ||
	   (relayable = valueeq(state->values[P_A_RELAYTARGET], "+"))) {

      /* Ok, local domain recognized, now see if it has
	 '%'-hack at the local-part.. */

      const unsigned char *phack, *phack2;
      int llen;

      --loopbreak;
      if (loopbreak <= 0) {
	type(NULL,0,NULL,"pt_rcptto('%.*s') loop break reached",
	     len, str);
	return -1;
      }

      llen = (at - str);

      /* How about '!' ??? */
      phack = find_nonqchr(str, '!', llen);
      if (phack && percent_accept < 0) {
	/* Bang-path from left to right... */
	/* ... each component from str to phack-1 */
	/* state->request initialization !! */
	state->request = ( 1 << P_A_RELAYTARGET     |
			   1 << P_A_ACCEPTbutFREEZE |
			   1 << P_A_ACCEPTifMX      |
			   1 << P_A_ACCEPTifDNS     |
			   1 << P_A_TestRcptDnsRBL  |
			   1 << P_A_LocalDomain );

	llen = (phack - str);
	if (check_domain(state, str, llen) != 0)
	  return -1;
	
	str = phack+1;
	continue;
      }

      /* Find the LAST of unquoted '%' characters! */
      phack = find_nonqchr(str, '%', llen);
      phack2 = NULL;
      while (phack && !phack2) {
	int ll2 = at - phack -1;
	phack2 = find_nonqchr(phack+1, '%', ll2);
	if (phack2) {
	  phack = phack2;
	  phack2 = NULL;
	} else
	  break; /* Not found */
      }
      /* Now do test of the domain in there, is it ok
	 for relaying to ? */
      if (phack) {
	/* state->request initialization !! */
	state->request = ( 1 << P_A_RELAYTARGET     |
			   1 << P_A_ACCEPTbutFREEZE |
			   1 << P_A_ACCEPTifMX      |
			   1 << P_A_ACCEPTifDNS     |
			   1 << P_A_TestRcptDnsRBL  |
			   1 << P_A_LocalDomain );

	llen = (at - phack)-1;
	if (check_domain(state, phack+1, llen) != 0)
	  return -1;
	at = phack;
	*((int*)&len) = (1 + at - str) + llen;
	continue;
      }

      if (phack && percent_accept < 0) {
	return -2; /* Reject the percent kludge */
      }

      break; /* Ok, could be ok, but RBL may say differently ... */
    }


    /* Do target specific rejects early */

    if (valueeq(state->values[P_A_RELAYTARGET], "-")) {
      PICK_PA_MSG(P_A_RELAYTARGET);
      return -1;
    }

    if (valueeq(state->values[P_A_ACCEPTbutFREEZE], "+")) {
	state->sender_freeze = 1;
	PICK_PA_MSG(P_A_ACCEPTbutFREEZE);
	return  1;
    }

    if (valueeq(state->values[P_A_TestRcptDnsRBL], "+")) {

      type(NULL, 0, NULL, "test-rcpt-dns-rbl test; rblmsg='%s'",
	   state->rblmsg ? state->rblmsg : "<none>");

      if (state->rblmsg != NULL) {
	/* Now this is cute... the source address had RBL entry,
	   and the recipient domain had a request to honour the
	   RBL data. */
	if (state->message != NULL) free(state->message);
	state->message = strdup(state->rblmsg);
	if (debug)
	  type(NULL,0,NULL," ... TestRcptDnsRBL has a message: '%s'",
		 state->rblmsg);
	return -1;
      }
    }

    if (valueeq(state->values[P_A_RELAYTARGET], "+")) {
	PICK_PA_MSG(P_A_RELAYTARGET);
	return  0;
    }

    if (state->always_accept) {
      int rc, c = '-';

      if (state->values[P_A_ACCEPTifMX]) {
	c = state->values[P_A_ACCEPTifMX][0];
      }
      rc = client_dns_verify( state, c, (const char *)at+1,
			      len - (1 + at - str) );
      /* XX: state->message setup! */
      if (debug)
	type(NULL,0,NULL," ... returns: %d", rc);
      PICK_PA_MSG(P_A_ACCEPTifMX);
      return rc;
    }

    if (state->values[P_A_ACCEPTifMX] || state->sender_norelay != 0) {
      int c = state->values[P_A_ACCEPTifMX] ? state->values[P_A_ACCEPTifMX][0] : '.';
      int rc;
      time_t then;

      /* The getmxrr() testing will report, if
	 the target domain has just A record,
	 and it is one of ours. */
      state->islocaldomain = 0;

      time(&then);
      rc = mx_client_verify( state, c, (const char *)at+1,
			     len - (1 + at - str) ); 
      time(&now);
      if ((now - then) > 30)
	type(NULL,0,NULL,"MX_CLIENT_VERIFY() TOOK %d SECONDS!",
	     (int)(now - then));

      /* XX: state->message setup! */
      if (debug)
	type(NULL,0,NULL,
	     " ...(mx_client_verify('%.*s')) returns: %d; lcldom=%d",
	     (int)(len - (1 + at - str)), at+1, rc, state->islocaldomain);

      if (state->islocaldomain) {
	const unsigned char *phack;
	int llen = (at - str);

	/* Simulate proper 'localnames' listing for this domain! */
	if (state->values[P_A_LocalDomain])
	  free(state->values[P_A_LocalDomain]);
	state->values[P_A_LocalDomain] = strdup("+");

	/* Hmm..  Recognize if we need to spin-back to %-hack, or !-hack */

	phack = find_nonqchr(str, '!', llen);
	if (phack)
	  goto process_local_domain;
	phack = find_nonqchr(str, '%', llen);
	if (phack)
	  goto process_local_domain;

	/* Ok, local, but not %-hack or !-hack, let it fall thru to
	   accept-if-mx */

      }

      PICK_PA_MSG(P_A_ACCEPTifMX);
      return rc;
    }

    if (state->values[P_A_ACCEPTifDNS]) {
      time_t then;
      int rc;
      time(&then);
      rc = client_dns_verify( state, state->values[P_A_ACCEPTifDNS][0],
			      (const char *)at+1, len - (1 + at - str));
      time(&now);
      if ((now - then) > 30)
	type(NULL,0,NULL,"CLIENT_DNS_VERIFY() TOOK %d SECONDS!",
	     (int)(now - then));
      /* XX: state->message setup! */
      if (debug)
	type(NULL,0,NULL," ... returns: %d", rc);
      PICK_PA_MSG(P_A_ACCEPTifDNS);
      return rc;
    }

    return 0;
}

static int pt_rcptpostmaster(state, str, len)
     struct policystate *state;
     const unsigned char *str;
     const int len;
{
    /* state->request initialization !! */
    state->request = ( 1 << P_A_RELAYTARGET );

    if (check_user(state, str, len) == 0) {
      if (valueeq(state->values[P_A_RELAYTARGET], "+")) {
	PICK_PA_MSG(P_A_RELAYTARGET);
	return  0;
      }
    }
    return -1;
}


int policytest(state, what, str, len, authuser)
     struct policystate *state;
     PolicyTest what;
     const char *str, *authuser;
     const int len;
{
    int rc;
    int d;
    if (state == NULL || state->PT == NULL)
      return 0;

    if (state->authuser == NULL)
	state->authuser = (char*)authuser;

    if (debug) {
	type(NULL,0,NULL," policytest what=%d", what);
	printstate(state);
    }

    if (state->message != NULL)
	free(state->message);
    state->message = NULL;

    switch(what) {
    case POLICY_SOURCEDOMAIN:
	rc = pt_sourcedomain(state, (const unsigned char *)str, len);
	break;
    case POLICY_HELONAME:
	rc = pt_heloname(state, (const unsigned char *)str, len);
	break;
    case POLICY_MAILFROM:
	d = debug;
	/* debug = 1; */
	rc = pt_mailfrom(state, (const unsigned char *)str, len);
	debug = d;
	break;
    case POLICY_RCPTTO:
	d = debug;
	/* debug = 1; */
	rc = pt_rcptto(state, (const unsigned char *)str, len);
	debug = d;
	break;
    case POLICY_RCPTPOSTMASTER:
	rc = pt_rcptpostmaster(state, (const unsigned char *)str, len);
	break;
    case POLICY_DATA:
    case POLICY_DATAOK:
	rc = call_rate_counter(state, len, POLICY_DATAOK, NULL, NULL);
	/* type(NULL,0,NULL," call_rate_counter(): DATAOK: i=%d",len); */
	break;
    case POLICY_DATAABORT:
	rc = call_rate_counter(state, len, POLICY_DATAABORT, NULL, NULL);
	/* type(NULL,0,NULL," call_rate_counter(): DABORT: i=%d",len); */
	break;
    case POLICY_AUTHFAIL:
	/* FIXME: usernamestr, or NULL, is available at the 'str' .. */
	rc = call_rate_counter(state, len, POLICY_AUTHFAIL, NULL, NULL);
	/*type(NULL,0,NULL," call_rate_counter(): AUTHFAIL: i=%d",len);*/
	break;
    default:
	abort();		/* Code error! Bad policy !	*/
	return 9999;		/* To silence most compilers..	*/
    }
    if (debug) fflush(stdout);
    return rc;
}

char *
policymsg(state)
     struct policystate *state;
{
    return state->message;
}

#ifdef Z_CHECK_SPF_DATA
char *
policyspfhdr(state)
     struct policystate *state;
{
    return state->spf_received_hdr;
}
#endif

long
policyinsizelimit(state)
     struct policystate *state;
{
    return state->maxinsize;
}

long
policysameiplimit(state)
     struct policystate *state;
{
    return state->maxsameiplimit;
}
