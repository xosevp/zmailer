# Generated automatically from Makefile.in by configure.
# Master Makefile for the ZMailer

MAJORVERSION =	2
MINORVERSION =	99
PATCHLEVEL =	49p10-s6

srcdir = .


ZCONFIG = /etc/zmailer.conf
ZCONF   = ./zmailer.Config
#ZDEPEND = Dependencies
CPPDEP  =  gcc -MM

SHELL = /bin/sh

DISTFILES = COPYING COPYING.LIB ChangeLog Makefile.in README INSTALL \
NEWS configure configure.in config.h.in mkinstalldirs install-sh \
stamp-h.in acconfig.h

# Redundant stuff for making only selected programs.
PROGS	= router/router scheduler/scheduler			\
	scheduler/mailq smtpserver/smtpserver transports/-ok	\
	compat/rmail/rmail compat/sendmail/sendmail		\
	utils/vacation/vacation utils/makedb/makedb

# Subdirectories to run make in for the primary targets.
SUBDIRS =  smtpserver router scheduler transports compat utils
# Subdirectories where to run 'make clean'
MOREDIRS = libs lib libc libsh libident libmalloc libresolv ssl \
	   proto doc man
# Files to remove in cleanup
CLEANFILES = include/rfc822.entry $(ZCONF) version.c

DISTCLEANFILES = include/mail.h SiteConfig bin/mklibdeb bin/mkdeb	\
		utils/zmailer.init.sh	proto/cf/SMTP+UUCP.cf	\
		proto/cf/TELE-FI.cf	proto/cf/UTdefault.cf	\
		proto/db/aliases				\
		man/Makefile		proto/db/Makefile	\
		bin/mkdep		bin/mklibdep

#.SUFFIXES:

all: config.h Makefile rfc822.entry $(ZCONF) SiteConfig
	rm -f libs/libtag
	for subdir in $(SUBDIRS); do \
		echo making $@ in $$subdir; \
		(cd $$subdir && $(MAKE) $@) || exit 1; \
	done

info dvi:
	cd doc && $(MAKE) $@

check:
installcheck:

rfc822.entry: include/rfc822.entry

include/rfc822.entry:
	cd router ; $(MAKE) $(MFLAGS) rfc822.entry

install-cf:	# all
	@. $(ZCONF) ; if [ -f $$ZCONFIG ] ; then	\
	 cmp -s $(ZCONF) $(prefix)$$ZCONFIG ||		\
	   echo "**" && echo "** Please consider copying $(ZCONF) to $(prefix)$$ZCONFIG !" && echo "**";\
	else						\
		cp $(ZCONF) $(prefix)$$ZCONFIG; chmod 644 $(prefix)$$ZCONFIG; \
	fi
	cd proto ;	$(MAKE) $(MFLAGS) cf

install-bin:	# all
	@. $(ZCONF) ; if [ -f $$ZCONFIG ] ; then	\
	 cmp -s $(ZCONF) $(prefix)$$ZCONFIG ||		\
	   echo "**" && echo "** Please consider copying $(ZCONF) to $(prefix)$$ZCONFIG !" && echo "**";\
	else						\
		cp $(ZCONF) $(prefix)$$ZCONFIG; chmod 644 $(prefix)$$ZCONFIG; \
	fi
	cd proto ;      $(MAKE) $(MFLAGS) install-bin  PZCONFIG="../$(ZCONF)"
	cd compat ;     $(MAKE) $(MFLAGS) install
	cd router ;     $(MAKE) $(MFLAGS) install
	cd scheduler ;  $(MAKE) $(MFLAGS) install
	cd smtpserver ; $(MAKE) $(MFLAGS) install
	cd transports ; $(MAKE) $(MFLAGS) install
	cd libc ;       $(MAKE) $(MFLAGS) install
	cd utils ;      $(MAKE) $(MFLAGS) install
	@. $(ZCONF) ; echo "** Please make sure the $$ZCONFIG -file is up to date!"

dirs:
	cd proto ; $(MAKE) $(MFLAGS) dirs PZCONFIG="../$(ZCONF)"

install:	dirs # all
	. $(ZCONF) ; cp $(ZCONF) $(prefix)$$ZCONFIG ; chmod 644 $(prefix)$$ZCONFIG
	cd proto ;      $(MAKE) $(MFLAGS) install  PZCONFIG="../$(ZCONF)"
	cd compat ;     $(MAKE) $(MFLAGS) install
	cd router ;     $(MAKE) $(MFLAGS) install
	cd scheduler ;  $(MAKE) $(MFLAGS) install
	cd smtpserver ; $(MAKE) $(MFLAGS) install
	cd transports ; $(MAKE) $(MFLAGS) install
	cd libc  ;      $(MAKE) $(MFLAGS) install
	cd utils ;      $(MAKE) $(MFLAGS) install

router/router:
	cd router ; $(MAKE) $(MFLAGS) router-a

scheduler/scheduler:
	cd scheduler ; $(MAKE) $(MFLAGS) all

scheduler-old/scheduler-old:
	cd scheduler-old ; $(MAKE) $(MFLAGS) all

scheduler/mailq:
	cd scheduler ; $(MAKE) $(MFLAGS) all

smtpserver/smtpserver:
	cd smtpserver ; $(MAKE) $(MFLAGS) smtpserver-a

compat/rmail/rmail:
	cd compat ; $(MAKE) $(MFLAGS) rmail/rmail-always

compat/sendmail/sendmail:
	cd compat ; $(MAKE) $(MFLAGS) sendmail/sendmail-always

utils/vacation/vacation:
	cd utils/vacation ; $(MAKE) $(MFLAGS) vacation

utils/makedb/makedb:
	cd utils/makedb ; $(MAKE) $(MFLAGS)

lib/libz.a: lib/*.c
	cd lib ; $(MAKE) $(MFLAGS)

libc/libzc.a: libc/*.c
	cd libc ; $(MAKE) $(MFLAGS)

libauth/libauth.a: libauth/authuser.c libauth/authuser.h
	cd libauth; $(MAKE) $(MFLAGS)

libresolv/libresolv.a: libresolv/*.c
	cd libresolv; $(MAKE) $(MFLAGS)

transports/libta/libta.a: transports/libta/*.c
	cd transports/libta ; $(MAKE) $(MFLAGS)

transports/-ok:
	cd transports ; $(MAKE) $(MFLAGS)

mostlyclean: mostlyclean-recursive mostlyclean-local

clean: clean-recursive clean-local

distclean: distclean-recursive distclean-local
	: rm config.status

realclean: realclean-recursive realclean-local
	: rm config.status

TAGS clean-recursive distclean-recursive \
	    mostlyclean-recursive realclean-recursive:
	for subdir in $(SUBDIRS) $(MOREDIRS); do \
	  target=`echo $@|sed 's/-recursive//'`; \
	  echo making $$target in $$subdir; \
	  (cd $$subdir && $(MAKE) $$target) || exit 1; \
	done
	rm -f $(CLEANFILES)

mostlyclean-local:

clean-local: mostlyclean-local
	-tt=`find . "(" -name "*~" -o -name "*.log" -o -name "*.orig" ")" -print` && \
		rm -f clean.state $$tt

clean-version:
	-rm -f `find . -name version.c -print | egrep -v libmalloc` dummy.name
	-rm -f `find . -name revision -print ` dummy.name

distclean-local: clean-local clean-version
	rm -f config.cache config.h config.log stamp-h distname
	rm -f $(DISTCLEANFILES)

realclean-local: distclean-local

neat:
	-rm -f $(ZCONF) $(CONF).sed eddep makedep Makefile.bak *.tar

scrub:	distclean
	-rm -f make.log make.out make.err* errs

scrub-obsolete-tail:
	# No null entry at all, let it be generated into proper form
	# when real processing goes thru..
	# @echo 'typedef enum { nilHeaderSemantics = -1 } HeaderSemantics;' > include/rfc822.entry

dist:
	@echo 'Did you run "make scrub" first?' ; sleep 2
	chmod -R a+rX .
	find . -type d -o -type f -print | \
	  egrep -v -e '/(private[/$$]|config.cache|config.status|RCS[/$$]|ID$$|.*\.o$$|fc[/$$]|.*\.a$$)' | \
	  CWD=`pwd` sed -e '/\.tar.*/d' -e "s/^\./`sh -c 'basename \`pwd\`'`/" | \
	  sort -t/ > MANIFEST
	cp MANIFEST /tmp
	(cd .. ; tar cvf - `cat /tmp/MANIFEST` ) > `basename \`pwd\``.tar
	rm -f /tmp/MANIFEST #MANIFEST


# For the justification of the following Makefile rules, see node
# `Automatic Remaking' in GNU Autoconf documentation.

SiteConfig Makefile: config.status Makefile.in
	CONFIG_FILES=$@ CONFIG_HEADERS= ./config.status

config.h: stamp-h
stamp-h: config.status $(srcdir)/config.h.in
	CONFIG_FILES= CONFIG_HEADERS=config.h ./config.status

config.status: configure
	./config.status --recheck
configure: configure.in
	cd $(srcdir) && autoconf
config.h.in: stamp-h.in
stamp-h.in: configure.in
# 	cd $(srcdir) && autoheader
# # Use echo instead of date to avoid spurious conflicts for
# # people who use CVS, since stamp-h.in is distributed.
# 	echo > $(srcdir)/$@

$(ZCONF):	SiteConfig
	(echo '# Do not edit this file, instead edit '`pwd`'/SiteConfig.in file'; \
	cat SiteConfig | \
	sed -n	-e '/^\([a-zA-Z][^ 	]*\)[ 	]*=[ 	]*\(.*\)[ 	]*$$/!d' \
		-e 's/^\([^ 	]*\)[ 	]*=[ 	]*\(.*\)[ 	]*$$/\1="\2"/' \
		-e 's/^\([^=]*\)=""\(.*\)""$$/\1="\2"/'	\
		-e 's/^\([^=]*\)="\([^ 	]*\)"$$/\1=\2/'			\
		-e p	) > $@
# The sed-patterns above do:
#  - match sh-variable set expression, discard all else
#  - pick the variable name, and the parameter string and form up
#    an expression:   VAR="DATA"
#  - if the newly made expression has double quotes (because the input
#    was quoted), remove the extra quotes
#  - if a value is quoted, and it does not have white-space in it, strip
#    the quotes away
#  - and as always with sed, "p" in the end to output the result

#OLD OLD OLD OLD OLD OLD OLD OLD OLD OLD OLD OLD OLD OLD
# $(ZCONF):	SiteConfig
# 	(echo '# Do not edit this file, instead edit '`pwd`'/SiteConfig.in file'; \
# 	cat SiteConfig | \
# 	sed -n  -e '/^[^ 	]*=[ 	]*[^#].*/!d' \
# 		-e 's:^\([^ 	]*\)=[ 	]*\([^#].*\):\1=\2:' \
# 		-e 's:=\([^# 	]*[ 	][^#]*\)\(.*\):="\1"\2:' \
# 		-e 's:\([ 	][ 	]*\)":"\1:' \
# 		-e 's:"\([^ 	]*\)":\1:' -e 's:""::' -e p   ) > $@

force:

version.c: force # Makefile
	@sh -c ': $${USER=$${LOGNAME-root}} ; \
	REVISION=`cat revision 2>/dev/null || (echo 0 | tee revision)` ; \
	HOSTNAME=`(/bin/hostname || /bin/uname) 2>/dev/null` ; \
	case "$$REVISION" in \
	[0-9]|[0-9][0-9]|[0-9][0-9][0-9]) \
		REVISION=`expr $$REVISION + 1` ;; \
	*)	REVISION=0 ;; \
	esac ; \
	case "${PATCHLEVEL}" in \
	0)	VERSION="${MAJORVERSION}.${MINORVERSION}" ;; \
	*)	VERSION="${MAJORVERSION}.${MINORVERSION}.${PATCHLEVEL}" ;; \
	esac ; \
	echo $$REVISION > revision ; \
	exec > version.c ; \
	echo "const char *Version = \"$${VERSION} #$${REVISION}: `date`\";"; \
	echo "const char *VersionNumb = \"$${VERSION} #$${REVISION}\";"; \
	echo "const char *CC_user = \"$${USER}@$${HOSTNAME}\";"; \
	echo "const char *CC_pwd = \"`pwd`\";" '

depend:
	for x in $(SUBDIRS) $(MOREDIRS); do		\
	    if [ -f $$x/Makefile ]; then		\
		( cd $$x; ${MAKE} ${MFLAGS} depend CPPDEP="${CPPDEP}" ); \
	    fi ;					\
	done


# Tell versions [3.59,3.63) of GNU make not to export all variables.
# Otherwise a system limit (for SysV at least) may be exceeded.
.NOEXPORT:

# DO NOT DELETE THIS LINE -- It is used by 'make depend' to update this file
