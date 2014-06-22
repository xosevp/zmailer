/*
 *  ZMailer smtpserver,  AUTH command things;
 *  part of ZMailer.
 *
 *  by Matti Aarnio <mea@nic.funet.fi> 1999
 *  Magnus Sjögren <dat98msj@student3.lu.se> did PAM
 */

/*
 *  This does plaintext-login authentication, *NOT* any of more
 *  advanced things, e.g. AUTH CRAM-MD5 ...
 *
 *  Codes compiled in are in order:
 *  - <security/pam_appl.h> -- generic PAM application
 *        See:  doc/guides/smtpauth-login-pam-support
 *  - Generic SHADOW application
 *  - plain classical  getpwnam()  application
 */

#define _GNU_SOURCE /* Very short hand define to please compilation
		       at glibc 2.1.* -- _XOPEN_SOURCE_EXTENDED + BSD + ... */

#include "mailer.h"

#include <sys/types.h>

#if defined(HAVE_SECURITY_PAM_APPL_H) && !defined(NO_SECURITY_PAM)
# include <security/pam_appl.h>
#else
# if defined(HAVE_SHADOW_H) && !defined(NO_SHADOW)
#  include <shadow.h>
# endif /* HAVE_SHADOW_H */
# include <pwd.h>
#endif /* HAVE_SECURITY_PAM_APPL_H */

#include <unistd.h>
#include <string.h>
#include "libz.h"

extern char * zpwmatch __((const char *, const char *, long *));

#if defined(HAVE_SECURITY_PAM_APPL_H) && !defined(NO_SECURITY_PAM)

static char *username = NULL;
static char *pword = NULL;

static void clean_reply __((int, const struct pam_message **, struct pam_response *));
static void clean_reply(int num_msg, const struct pam_message **msg,
			struct pam_response *reply)
{
    int count = 0;

    if (reply) {
        for (count = 0; count < num_msg; ++count) {
            if (reply[count].resp == NULL) {
                continue;
            }
	    switch (msg[count]->msg_style) {
            case PAM_PROMPT_ECHO_ON:
            case PAM_PROMPT_ECHO_OFF:
		memset(reply[count].resp, 0, strlen(reply[count].resp));
                free(reply[count].resp);
                break;
            case PAM_ERROR_MSG:
            case PAM_TEXT_INFO:
                free(reply[count].resp);
		break;
            }
            reply[count].resp = NULL;
        }
        free(reply);
        reply = NULL;
    }
}

/** WARNING:  Linux vs. Solaris:
      Linux   = const struct pam_message **
      Solaris =       struct pam_message **
**/

static int
pam_cons __((int, const struct pam_message **,
	     struct pam_response **, void *));

static int
pam_cons(num_msg, msg, resp, appdata_ptr)
     int num_msg;
     const struct pam_message **msg;
     struct pam_response **resp;
     void *appdata_ptr;
{
    int count = 0;
    struct pam_response *reply;

    if (num_msg <= 0)
        return PAM_CONV_ERR;

    reply = (struct pam_response *) calloc(num_msg, 
					   sizeof(struct pam_response));
    if (reply == NULL)
        return PAM_CONV_ERR;
    
    for (count = 0; count < num_msg; ++count) {
	switch (msg[count]->msg_style) {
        case PAM_PROMPT_ECHO_ON:
            reply[count].resp_retcode = 0;
            reply[count].resp = strdup(username);
            break;
        case PAM_PROMPT_ECHO_OFF:
	    reply[count].resp_retcode = 0;
	    reply[count].resp = strdup(pword);
	    break;
        case PAM_TEXT_INFO: /* These cases should never happen */
	case PAM_ERROR_MSG:
	    reply[count].resp_retcode = 0;
	    reply[count].resp = NULL;
            break;
	default: /* This should never happen */
	    clean_reply(num_msg, msg, reply);
	    return PAM_CONV_ERR;
	}
    }
    *resp = reply;
    reply = NULL;
    return PAM_SUCCESS;
}

/* yes, following will complain in some systems..
   details on constness of PAM routines have varied
   greatly, for example. */
static struct pam_conv pam_c = {
    pam_cons,
    NULL
};

char * zpwmatch(uname,password,uidp)
     const char *uname, *password;
     long *uidp;
{
    pam_handle_t *ph;
    int ret, val;

    username = strdup(uname);
    pword = strdup(password);
    
    runasrootuser();
    ret = pam_start("smtpauth-login", username, &pam_c, &ph);
    /* type(NULL,0,NULL,"pam_start() ret=%d", ret); */

    if (ret == PAM_SUCCESS) {
	ret = pam_authenticate(ph, 0);
	/* type(NULL,0,NULL,"pam_authentication() ret=%d",ret); */
    }
#if 0
    if (ret == PAM_SUCCESS) {
	ret = pam_acct_mgmt(ph, 0);
	/* type(NULL,0,NULL,"pam_acct_mgmt() ret=%d",ret); */
    }
#endif
    val = ret;
    if ((ret = pam_end(ph, ret)) != PAM_SUCCESS) {
	/* type(NULL,0,NULL,"pam_end() ret=%d",ret); */
	ph = NULL;
    }
    runastrusteduser();

    if (username) {
	memset(username, 0, strlen(username));
	free(username);
	username = NULL;
    }
    if (pword) {
	memset(pword, 0, strlen(pword));
	free(pword);
	pword = NULL;
    }

    return (val == PAM_SUCCESS) ? NULL : "Authentication Failed";
}

#else
# if defined(HAVE_SHADOW_H) && !defined(NO_SHADOW)

char * zpwmatch(uname, password, uidp)
     const char *uname, *password;
     long *uidp;
{
    struct spwd *spw;
    struct passwd *pw;
    int ok = 0;
    
    runasrootuser();

    if (lckpwdf() == -1) {
	spw = NULL; /* Lock failed.. */
    } else {
	spw = getspnam(uname);
	ulckpwdf(); /* Unlock */
    }

    pw = getpwnam(uname); /* Do this as root user, just in case.. */

    runastrusteduser();

    if (pw) { 

      /* Either the   getpwnam()  returns working password out of
	 the shadow dataset, or a third-party shadow set must be used
	 to pick also the encrypted data..  Both fetches are done,
	 and now we do comparisons presuming the first fetch result
	 is usable encrypted password ...
	 (Thanks to Eugene Crosser for report.)
      */

      char *cr = crypt(password, pw->pw_passwd);

      if (cr != NULL && strcmp(cr, pw->pw_passwd) == 0)
	ok = 1;
      else if (spw) {
	/* Ok, perhaps the second one contains usable encrypted password ? */
	cr = crypt(password, spw->sp_pwdp);
	if (cr != NULL && strcmp(cr, spw->sp_pwdp) == 0)
	  ok = 1;
      }

      *uidp = pw->pw_uid;
    }

    return (ok ? NULL : "Authentication Failed");
}

# else

char * zpwmatch(uname,password,uidp)
     const char *uname, *password;
     long *uidp;
{
    struct Zpasswd *pw;
    char *cr;

    runasrootuser();

    pw = zgetpwnam(uname);

    runastrusteduser();

    if (pw) {
      cr = crypt(password, pw->pw_passwd);
      *uidp = pw->pw_uid;
    }

    return ((pw && cr && (strcmp(cr, pw->pw_passwd) == 0))
	    ? NULL : "Authentication Failed");
}
# endif /* HAVE_SHADOW_H */
#endif
