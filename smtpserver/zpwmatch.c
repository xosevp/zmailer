/*
 *  ZMailer smtpserver,  AUTH command things;
 *  part of ZMailer.
 *
 *  by Matti Aarnio <mea@nic.funet.fi> 1999
 *  Magnus Sj�gren <dat98msj@student3.lu.se> did PAM
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

#ifdef HAVE_SECURITY_PAM_APPL_H
# include <security/pam_appl.h>
#else
# ifdef HAVE_SHADOW_H
#  include <shadow.h>
# endif /* HAVE_SHADOW_H */
# include <pwd.h>
#endif /* HAVE_SECURITY_PAM_APPL_H */

#include <unistd.h>
#include <string.h>
#include "libz.h"

#ifdef HAVE_SECURITY_PAM_APPL_H

static char *username = NULL;
static char *pword = NULL;

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
                bzero(reply[count].resp, strlen(reply[count].resp));
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

static int pam_cons(int num_msg, const struct pam_message **msg,
		    struct pam_response **resp, void *appdata_ptr)
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

static struct pam_conv pam_c = {
    pam_cons,
    NULL
};

int zpwmatch(uname,password,uidp)
     char *uname, *password;
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

    if (ret == PAM_SUCCESS) {
	ret = pam_acct_mgmt(ph, 0);
	/* type(NULL,0,NULL,"pam_acct_mgmt() ret=%d",ret); */
    }

    val = ret;
    if ((ret = pam_end(ph, ret)) != PAM_SUCCESS) {
	/* type(NULL,0,NULL,"pam_end() ret=%d",ret); */
	ph = NULL;
    }
    runastrusteduser();

    if (username) {
	bzero(username, strlen(username));
	free(username);
	username = NULL;
    }
    if (pword) {
	bzero(pword, strlen(pword));
	free(pword);
	pword = NULL;
    }

    return (val == PAM_SUCCESS) ? 1 : 0;
}

#else
# ifdef HAVE_SHADOW_H

int zpwmatch(uname, password, uidp)
     char *uname, *password;
     long *uidp;
{
    struct spwd *spw;
    struct passwd *pw;
    char *cr;
    
    runasrootuser();

    if (lckpwdf() == -1) {
	spw = NULL;
    } else
	spw = getspnam(uname);
    ulckpwdf(); /* Not much we can do here anyway if it fails */

    runastrusteduser();

    if (!spw) return 0; /* No such user */
    pw = getpwnam(uname);
    if (!pw) return 0;  /* No such user! HUH! (had shadow-entry, though!) */
    cr = crypt(password, spw->sp_pwdp);
    *uidp = pw->pw_uid;

    return (strcmp(cr, spw->sp_pwdp) == 0);
}

# else

int zpwmatch(uname,password,uidp)
     char *uname, *password;
     long *uidp;
{
    struct passwd *pw;
    char *cr;

    runasrootuser();

    pw = getpwnam(uname);

    runastrusteduser();

    if (!pw) return 0; /* No such user */
    cr = crypt(password, pw->pw_passwd);
    *uidp = pw->pw_uid;

    return (strcmp(cr, pw->pw_passwd) == 0);
}
# endif /* HAVE_SHADOW_H */
#endif
