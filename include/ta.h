/*
 *	Copyright 1990 by Rayan S. Zachariassen, all rights reserved.
 *	This will be free software, but only when it is finished.
 */
/*
 *	A plenty of changes, copyright Matti Aarnio 1990-1995
 */

#ifndef _Z_TA_H_
#define _Z_TA_H_

#ifdef HAVE_CONFIG_H
#include "hostenv.h"
#endif

struct taddress {
	struct taddress	*link;		/* next sender / sender for this rcpt */
	const char	*channel;
	const char	*host;
	const char	*user;
	const char	*misc;		/* expected to be uid privilege */
	const char	**routermxes;	/* [mea] hostpointers from router */
};

#define _DSN_NOTIFY_SUCCESS	0x001
#define _DSN_NOTIFY_FAILURE	0x002
#define _DSN_NOTIFY_DELAY	0x004
#define _DSN_NOTIFY_NEVER	0x008

#define _DSN__DIAGDELAYMODE	0x800 /* Internal magic */

/* `convertmode' controls the behaviour of the message conversion:
     _CONVERT_NONE (0): send as is
     _CONVERT_QP   (1): Convert 8-bit chars to QUOTED-PRINTABLE
     _CONVERT_8BIT (2): Convert QP-encoded chars to 8-bit
     _CONVERT_UNKNOWN (3): Turn message to charset=UNKNOWN-8BIT, Q-P..
*/
#define _CONVERT_NONE	 0
#define _CONVERT_QP	 1
#define _CONVERT_8BIT	 2
#define _CONVERT_UNKNOWN 3


struct rcpt {
	struct rcpt	*next;
	struct taddress	*addr;		/* addr.link is the sender address */
	const char	*orcpt;		/*  DSN  ORCPT=  string */
	const char	*inrcpt;	/* "DSN" INRCPT= string */
	const char	*notify;	/*  DSN  NOTIFY= flags  */
	int		notifyflgs;
	char		***newmsgheader; /* message header line pointer ptr
					   that points to an address of
					      ctldesc->msgheaders[index]
					   which then points to a place
					   containing the header itself.
					   Thus enabling rewrite of the
					   header on the transport. */
	char		***newmsgheadercvt; /* the rewrite results */
	int		id;		/* the index of this address */
	int		lockoffset;	/* the index of the address lock */
	int		headeroffset;
	int		drptoffset;
	int		status;		/* current delivery sysexit code */
	struct ctldesc	*desc;		/* backpointer to descriptor */
	/* XX: something needed for XOR address lists */

#if 0 /* not yet ?? */
	/* Delayed diagnostics */
	char		*diagdelaybuf;
	int		diagdelaysize;
	int		diagdelayspace;
#endif
};

struct ctldesc {
	const char	*msgfile;	/* message file name */
	const char	*logident;	/* message id for logging */
	const char	*verbose;	/* file for verbose logging */
	const char	*envid;		/* DSN ENVID data */
	const char	*dsnretmode;	/* DSN RET=-mode */
	time_t		msgmtime;	/* Message file arrival time */
	long		msgbodyoffset;	/* offset of message body in msgfile */
	long		msgsizeestimate; /* Estimate of the msg size */
	int		msgfd;		/* message file I/O descriptor */
	int		ctlfd;		/* control file I/O descriptor */
	int		ctlid;		/* control file id (inode number) */
	char		*ctlmap;	/* control file mmap() block */
	const char	*contents;	/* message file data */
	long		contentsize;	/* message file size */
	long		*offset;	/* array of indices into contents */
	struct taddress	*senders;	/* list of sender addresses */
	struct rcpt	*recipients;	/* list of selected recipients */
	int		rcpnts_total;	/* number of recipients, total */
	int		rcpnts_remaining;/* .. how many yet to deliver */
	int		rcpnts_failed  ;/* .. how many failed ones */
	char		***msgheaders;	/* pointer to all msg headers */
	char		***msgheaderscvt; /* converted headers */
#ifdef	HAVE_MMAP
	const char	*let_buffer;	/* MMAP()ed memory area containing */
	const char	*let_end;	/* the mail -- and its end..	   */
#endif
};


/* MIME-processing headers -- "Content-Transfer-Encoding:",
			  and "Content-Type:"			*/

struct cte_data {
	char	*encoder;
};

struct ct_data {
	char	*basetype;	/* "text"		*/
	char	*subtype;	/* "plain"		*/
	char	*charset;	/* charset="x-yzzy"	*/
	char	*boundary;	/* boundary="...."	*/
	char	*name;		/* name="..."		*/
	char	**unknown;	/* all unknown parameters */
};


struct mimestate {
	int	lastch;
	int	lastwasnl;
	int	convertmode;
	int	column;
	int	alarmcnt;
};


/* ctlopen.c: */
extern void            ctlfree __((struct ctldesc *dp, void *anyp));
extern void           *ctlrealloc __((struct ctldesc *dp, void *anyp, size_t size));
extern struct ctldesc *ctlopen __((const char *file, const char *channel, const char *host, int *exitflag, int (*selectaddr)(const char *, const char *, void *), void *saparam, int (*matchrouter)(const char *, struct taddress *, void *), void *mrparam));
extern void            ctlclose __((struct ctldesc *dp));
extern int	       ctlsticky __((const char *spec_host, const char *addr_host, void *cbparam));

/* diagnostic.c: */
extern const char     *notaryacct __((int rc, const char *okstr));
		/* NOTARY: addres / action / status / diagnostic  */
extern void 	       notaryreport __((const char*, const char*, const char*, const char*));
extern void            notary_setxdelay __((int));
extern void            notary_setwtt __(( const char *host ));
extern void            notary_setwttip __(( const char *ip ));
#if defined(HAVE_STDARG_H)
extern void	       diagnostic __((struct rcpt *rp, int rc, int timeout, const char *fmt, ... ));
#else
extern void	       diagnostic __((/* struct rcpt *, int, int, char *,... */));
#endif


#ifdef HOST_NOT_FOUND /* Defines 'struct hostent' ... */
# include "dnsgetrr.h"
#endif

/* emptyline.c: */
extern int	       emptyline __(( char *line, int size ));

#if 0 /* actually better to include "libz.h" for this */
/* esyslib.c: */
extern int cistrcmp  __((const char *s1, const char *s2));
extern int cistrncmp __((const char *s1, const char *s2, int n));
extern int efstat  __((int fd, struct stat *stbuf));
extern int emkdir  __((const char *dirpath, int mode));
extern int eopen   __((const char *s, int f, int m));
extern int epipe   __((int fdarr[2]));
extern int eread   __((int fd, char *buf, int len));
extern int estat   __((const char *filename, struct stat *stbuf));
extern int eunlink __((const char *filename));
extern int errno;
extern int optind;
extern int embytes;
extern int emcalls;
extern unsigned emsleeptime;
extern void * emalloc  __((size_t len));
extern void * erealloc __((void * buf, size_t len));
#ifdef S_IWUSR /* Defined on <sys/stat.h> */
extern int efstat __((int fd, struct stat *stbuf));
#endif
extern long elseek __((int fd, off_t pos, int action));
extern int elink __((const char *file1, const char *file2));
extern int eclose __((int fd));
extern int echdir __((const char *path));
extern int ermdir __((const char *path));
extern int erename __((char *from, char *to));
#endif

/* lockaddr.c: */
extern int lockaddr __((int fd, char *map, long offset, int was, int new, const char *file, const char *host, const int mypid));

/* markoff.c: */
extern int markoff __((char *filecontents, int bytesleft, long offsets[], const char *filename));

/* mimeheaders.c: */
#if defined(HAVE_STDARG_H)
extern int append_header __((struct rcpt *rp, const char *fmt, ...));
#else
extern int append_header __(());
#endif
extern struct cte_data *parse_content_encoding __((char **cte_linep));
extern struct ct_data  *parse_content_type __((char **ct_linep));
extern void output_content_type __((struct rcpt *rp, struct ct_data *ct, char **oldpos));
extern int check_conv_prohibit __((struct rcpt *rp));
extern int cte_check __((struct rcpt *rp));
extern char **has_header __((struct rcpt *rp, const char *keystr));
extern void delete_header __((struct rcpt *rp, char **hdrp));
extern int  downgrade_charset __((struct rcpt *rp, FILE *verboselog));
extern void downgrade_headers __((struct rcpt *rp, int downgrade, FILE *verboselog));
extern int qp_to_8bit __((struct rcpt *rp));

/* mime2headers.c */
extern int headers_to_mime2 __((struct rcpt *rp, const char *defcharset, FILE *verboselog));
extern int headers_need_mime2 __(( struct rcpt *rp ));
 

/* writeheaders.c: */
extern int writeheaders __((struct rcpt *rp, FILE *fp, const char *newline, int use_cvt, int maxwidth, char **chunkbufp));

/* buildbndry.c: */
extern char *mydomain __((void));
extern char *buildboundary __((const char *what));

extern int getout;
extern RETSIGTYPE wantout __((int));

/* warning.c */
#ifdef HAVE_STDARG_H
extern void warning __((const char *fmt, ...));
#else
extern void warning __(());
#endif

/* lib/skip821address.c */
extern char *skip821address __((const char *s));

/* tasyslog.c */
extern void tatimestr __((char *buf, int dt));
extern void tasyslog __((struct rcpt *rp, int xdelay, const char *wtthost, const char *wttip, const char *stats, const char *msg));

#ifndef CISTREQ
#define  CISTREQ(x, y)      (cistrcmp((const char *)(x), (const char *)(y)) == 0)
#define  CISTREQN(x, y, n)  (cistrncmp((const char *)(x), (const char *)(y), n) == 0)
#endif

extern int getmyuucename __((char *, int));

/* nonblocking.c */
extern int  fd_nonblockingmode __((int fd));
extern int  fd_blockingmode __((int fd));
extern void fd_restoremode __((int fd, int mode));

#endif
