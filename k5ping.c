/*  */

/*-
 * Copyright 2009  Morgan Stanley and Co. Incorporated
 * Copyright 2013  Roland C. Dowdeswell
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject
 * to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR
 * ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
 * CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <netdb.h>
#include <errno.h>

#include <sys/types.h>
#include <sys/socket.h>

#include <krb5.h>

#ifdef HAVE_KRB4
#include <kerberosIV/krb.h>
#endif

/*
 * Prototypes.
 */

static void	usage(void);
static void	fail_msg(const char *, int, const char *, const char *);
static void	parse_kdc(const char *host);
static int	kvno4(krb5_context, const char *, krb5_principal);
static int	kvno5(krb5_context, const char *, int, krb5_principal,
		      krb5_principal, krb5_ccache);
static int	k5ping(krb5_context, const char *, int, krb5_principal,
		       int, const char *, krb5_principal);
#ifdef HAVE_KRB4
static int	k4ping(krb5_context, const char *, krb5_principal, const char *,
		       krb5_principal);
static int	k524ping(krb5_context, const char *, const char *);
#endif

/*
 * Macros.  These can be set at each individual site.
 */

#define PING_PRINC	"k5ping_princ"
#define PING_PASSWD	"k5ping_passwd"

#define PING_SPRINC	"k5ping_princ"

/*
 * Global variables.
 */

char		*progname = NULL;

/* Mutable KDC information */
char	current_kdc[1024];
int	current_port;
int	current_secport;
int	current_socktype = SOCK_STREAM;
int	current_family = AF_INET;
int	force_udp = 0;
int	verbose = 0;

#define VERBOSE(x,y)	if (verbose >= (x)) fprintf y

#define K5BAIL_DECLS							\
		krb5_error_code	kret;					\
		char croakstr[2048] = "";

#define BAIL(x, y)	do {						\
		kret = x;						\
		if (kret) {						\
			snprintf(croakstr, sizeof(croakstr),		\
			    "%s: %s", #x, y);				\
			kret = 1;					\
			goto done;					\
		}							\
	} while (0)

#ifdef HAVE_HEIMDAL
#define K5BAIL(x)	do {						\
		kret = x;						\
		if (kret) {						\
			const char	*tmp;				\
									\
			tmp = krb5_get_error_message(ctx, kret);	\
			if (tmp) {					\
				snprintf(croakstr, sizeof(croakstr),	\
				    "%s: %s", #x, tmp);			\
				krb5_free_error_message(ctx, tmp);	\
			} else {					\
				snprintf(croakstr, sizeof(croakstr),	\
				    "%s: unknown error", #x);		\
			}						\
			kret = 1;					\
			goto done;					\
		}							\
	} while (0)
#else	
#define K5BAIL(x)	BAIL(x, error_message(kret))
#endif


/*
 * We over-ride the krb5_locate_kdc() function from -lkrb5 so that
 * we control both the horizontal and the verticle when it comes to
 * choosing which KDCs will be used.  As of MIT Kerberos 1.3, this
 * function takes socktype and family arguments.  We have two styles
 * here at the moment: ``OLD_MIT'' should work with 1.3-1.9 or so.
 * The default style should work with 1.10 and 1.11.
 */

#ifdef OLD_MIT	/* XXXrcd: need to define what versions. */

struct addrs {
	struct addrinfo *ai;
	void (*freefn)(void *);
	void *data;
};

struct addrlist {
	struct addrs *addrs;
	size_t naddrs;
	size_t space;
};

krb5_error_code
krb5_locate_kdc(krb5_context ctx, const krb5_data *realm,
                struct addrlist *addrlist, int get_masters,
		int socktype, int family)
{
	krb5_error_code	 ret;
	struct addrinfo	*addrs;
	struct addrinfo	*a;
	struct addrinfo	 hint;
	struct addrs	*al_addrs;
	char		 portbuf[16];
	size_t		 num;
	int		 err;

	VERBOSE(3, (stderr, "krb5_locate_kdc(context, \"%s\", addrlist, "
	    "%d, %d, %d ) called\n", realm->data, get_masters, socktype,
	    family));

	memset(addrlist, 0x0, sizeof(*addrlist));

	/*
	 * krb524d is always a udp service, so we if we are doing 524,
	 * then we hardwire to SOCK_DGRAM.
	 */

	if (socktype != 0 && ((!force_udp && socktype != current_socktype) ||
	    (force_udp && socktype != SOCK_DGRAM)))
		return KRB5_REALM_CANT_RESOLVE;

	memset(&hint, 0, sizeof(hint));
	hint.ai_family = family;
	hint.ai_socktype = socktype;
#ifdef AI_NUMERICSERV
	hint.ai_flags = AI_NUMERICSERV;
#endif

	snprintf(portbuf, sizeof(portbuf), "%d", ntohs(current_port));
	/* XXXrcd: errors... */

	err = getaddrinfo(current_kdc, portbuf, &hint, &addrs);
	if (err) {
		fprintf(stderr, "can't resolve %s:%s: %s\n",
		    current_kdc, portbuf, gai_strerror(err));
		return KRB5_REALM_CANT_RESOLVE;
	}

	for (num=0, a=addrs; a; a=a->ai_next, num++)
		;

	al_addrs = calloc(sizeof(*al_addrs) * num, 1);
	/* XXXrcd: errors... */

	for (num=0, a=addrs; a; a=a->ai_next, num++) {
		al_addrs[num].ai     = a;
		if (num == 0) {
			al_addrs[num].freefn = freeaddrinfo;
			al_addrs[num].data   = a;
		}
	}

	(*addrlist).addrs  = al_addrs;
	(*addrlist).naddrs = num;
	(*addrlist).space  = num;

	VERBOSE(3, (stderr, "krb5_locate_kdc(context, \"%s\", addrlist, "
	    "%d, %d, %d ) returning %d address(es)\n", realm->data,
	    get_masters, socktype, family, num));

	return 0;
}
#else
/* A single server hostname or address. */
struct server_entry {
    char *hostname;             /* NULL -> use addrlen/addr instead */
    int port;                   /* Used only if hostname set */
    int socktype;               /* May be 0 for UDP/TCP if hostname set */
    int family;                 /* May be 0 (aka AF_UNSPEC) if hostname set */
    size_t addrlen;
    struct sockaddr_storage addr;
}; 

/* A list of server hostnames/addresses. */
struct serverlist {
    struct server_entry *servers;
    size_t nservers;
};
#define SERVERLIST_INIT { NULL, 0 }

enum locate_service_type {
    locate_service_kdc = 1,
    locate_service_master_kdc, 
    locate_service_kadmin,
    locate_service_krb524,
    locate_service_kpasswd
}; 

krb5_error_code
k5_locate_server(krb5_context ctx, const krb5_data *realm,
		 struct serverlist *serverlist, enum locate_service_type svc,
		 int socktype)
{
	struct server_entry	*se;

	VERBOSE(3, (stderr, "k5_locate_server(ctx, \"%s\", serverlist, "
	    "%d, %d, %d ) called\n", realm->data, socktype));

	/*
	 * krb524d is always a udp service, so we if we are doing 524,
	 * then we hardwire to SOCK_DGRAM.
	 */

	if (socktype != 0 && ((!force_udp && socktype != current_socktype) ||
	    (force_udp && socktype != SOCK_DGRAM)))
		return KRB5_REALM_CANT_RESOLVE;

	VERBOSE(3, (stderr, "adding %s to the list...\n", current_kdc));

	se = calloc(sizeof(*se), 1);
	if (!se)
		return ENOMEM;

	se->hostname = strdup(current_kdc);
	se->port = current_port;
	se->socktype = current_socktype;
	se->family = AF_UNSPEC;

	serverlist->servers = se;
	serverlist->nservers = 1;

	if (!se->hostname) {
		free(se);
		return ENOMEM;
	}

	return 0;
}
#endif

#ifdef HAVE_KRB4
/*
 * We also over-ride krb_get_krbhst() in the same way.
 */

int
krb_get_krbhst(char *host, const char *realm, int n)
{

	VERBOSE(3, (stderr, "krb_get_krbhst(host, \"%s\", %d) called\n",
	    realm, n));

	if (n > 1)
		return KFAILURE;

	VERBOSE(3, (stderr, "krb_get_krbhst copying in %s\n", current_kdc));

	strcpy(host, current_kdc);
	return 0;
}
#endif

/* This function sets global variables */
static void
parse_kdc(const char *host)
{
	char	*tmp = NULL;

	strncpy(current_kdc, host, sizeof(current_kdc));
	current_kdc[sizeof(current_kdc) - 1] = '\0';

	current_port = htons(88);
	current_secport = 0;

	tmp = strchr(current_kdc, ':');
	if (tmp) {
		*tmp++ = '\0';
		current_port = htons(atoi(tmp));
	}

	VERBOSE(3, (stderr, "parse_kdc(%s): kdc = %s, port = %d\n", host,
	    current_kdc, ntohs(current_port)));
}

void
usage(void)
{

	fprintf(stderr, "usage: %s [-459tuv] [-p princ] [-P pass] "
	    "[-S sprinc]\n", progname);
	exit(1);
}

static void
fail_msg(const char *type, int socktype, const char *host, const char *error)
{

	fprintf(stderr, "k5ping(%s) ERROR - %s/%s ping failed: %s\n", host,
	    type, socktype == SOCK_DGRAM ? "udp" : "tcp", error);
}

#ifdef HAVE_KRB4
static int
kvno4(krb5_context ctx, const char *host, krb5_principal sprinc)
{
	krb5_error_code	kerr;
	KTEXT_ST	req;
	CREDENTIALS	creds;
	int		err = 0;
	char		name[ANAME_SZ];
	char		instance[INST_SZ];
	char		realm[REALM_SZ];

	VERBOSE(1, (stderr, "initiating kvno4/udp ping to %s\n", host));

	kerr = krb5_524_conv_principal(ctx, sprinc, name, instance, realm);
	if (kerr) {
		fail_msg("kvno4", SOCK_DGRAM, host, error_message(kerr));
		goto bail;
	}

	err = krb_mk_req(&req, name, instance, realm, 0);
	if (err)
		goto bail;

        err = krb_get_cred(name, instance, realm, &creds);
        if (err)
		goto bail;

	VERBOSE(2, (stderr, "%s.%s@%s kvno = %d\n", name, instance, realm,
	    creds.kvno));

bail:
	if (err)
		fail_msg("kvno4", SOCK_DGRAM, host, krb_get_err_text(err));
	return err;
}
#endif

static int
kvno5(krb5_context ctx, const char *host, int socktype, krb5_principal princ,
    krb5_principal sprinc, krb5_ccache ccache)
{
	krb5_error_code	 kerr = 0;
	krb5_creds	 increds;
	krb5_creds	*outcreds = NULL;
	krb5_ticket	*ticket = NULL;

	VERBOSE(1, (stderr, "initiating kvno5/%s ping to %s\n",
	    socktype == SOCK_DGRAM ? "udp" : "tcp", host));

	memset(&increds, 0x0, sizeof(increds));
	increds.client = princ;
	increds.server = sprinc;
	kerr = krb5_get_credentials(ctx, 0, ccache, &increds, &outcreds);
	if (kerr)
		goto bail;

        kerr = krb5_decode_ticket(&outcreds->ticket, &ticket);
        if (kerr)
		goto bail;

	VERBOSE(2, (stderr, "kvno5 says kvno = %d\n", ticket->enc_part.kvno));

bail:
	if (kerr)
		fail_msg("kvno5", socktype, host, error_message(kerr));
	if (ticket)
		krb5_free_ticket(ctx, ticket);
	if (outcreds)
		krb5_free_creds(ctx, outcreds);

	return kerr;
}

static int
k5ping(krb5_context ctx, const char *host, int socktype, krb5_principal princ,
    int use_kt, const char *passwd, krb5_principal sprinc)
{
	K5BAIL_DECLS;
	krb5_error_code		 kerr;
	krb5_ccache		 ccache = NULL;
	krb5_keytab		 kt;
	krb5_creds		 creds;
	krb5_get_init_creds_opt	*opt = NULL;

	VERBOSE(1, (stderr, "initiating kerberos5/%s ping to %s\n",
	    socktype == SOCK_DGRAM ? "udp" : "tcp", host));

	parse_kdc(host);
	current_socktype = socktype;

	K5BAIL(krb5_cc_resolve(ctx, "MEMORY:k5ping", &ccache));

        K5BAIL(krb5_get_init_creds_opt_alloc(ctx, &opt));
        krb5_get_init_creds_opt_set_tkt_life(opt, 15 * 60);

	if (use_kt) {
		K5BAIL(krb5_kt_default(ctx, &kt));
		K5BAIL(krb5_get_init_creds_keytab(ctx, &creds, princ, kt, 0,
		    NULL, opt));
	} else {
		K5BAIL(krb5_get_init_creds_password(ctx, &creds, princ, passwd,
		    krb5_prompter_posix, NULL, 0, NULL, opt));
	}

	K5BAIL(krb5_cc_store_cred(ctx, ccache, &creds));

	kret = kvno5(ctx, host, socktype, princ, sprinc, ccache);
done:
	if (ccache)
		krb5_cc_destroy(ctx, ccache);

	/* XXXrcd: free a few more things here... */
	/*	   opt.  creds.                   */

	if (croakstr[0])
		fail_msg("kerberos5", socktype, host, croakstr);

	return kret;
}

#if HAVE_KRB4
static int
k4ping(krb5_context ctx, const char *host, krb5_principal princ,
    const char *passwd, krb5_principal sprinc)
{
	krb5_error_code	kerr;
	int		ret;
	char		name[ANAME_SZ];
	char		instance[INST_SZ];
	char		realm[REALM_SZ];

	VERBOSE(1, (stderr, "initiating kerberos4/udp ping to %s\n", host));
	parse_kdc(host);
	kerr = krb5_524_conv_principal(ctx, princ, name, instance, realm);
	if (kerr) {
		fail_msg("kerberos4", SOCK_DGRAM, host, error_message(kerr));
		ret = 1;
		goto bail;
	}

	ret = krb_get_pw_in_tkt(name, instance, realm, "krbtgt",
	    realm, 3600 /* seconds */, (char *)passwd);
	if (ret) {
		fail_msg("kerberos4", SOCK_DGRAM, host, krb_get_err_text(ret));
		goto bail;
	}
	ret = kvno4(ctx, host, sprinc);
	/* XXXrcd */
	k_logout_k4(ctx, NULL, K_OPT_NONE);

bail:
	return ret;
}

static int
k524ping(krb5_context ctx, const char *host, const char *tsprinc)
{
	krb5_principal	 sprinc = NULL;
	CREDENTIALS	 v4creds;
	int		 kret;

	VERBOSE(1, (stderr, "initiating kerberos524/udp ping to %s\n", host));

	parse_kdc(host);

	/*
	 * Apparently, k_convert_creds_524() seems to corrupt
	 * sprinc...
	 */

	kret = krb5_parse_name(ctx, tsprinc, &sprinc);
	if (kret) {
		fprintf(stderr, "malformed princ %s: %s\n", tsprinc,
		    error_message(kret));
		exit(127);
	}

	force_udp = 1;
	kret = k_convert_creds_524(ctx, sprinc, &v4creds);
	force_udp = 0;
	if (kret) {
		fail_msg("kerberos524", SOCK_DGRAM, host, k_error_string(ctx));
		goto bail;
	}

bail:
#if 0
	krb5_free_principal(ctx, sprinc);
#endif
	return kret;
}
#endif

int
main(int argc, char **argv)
{
	K5BAIL_DECLS;
	krb5_context	 ctx;
	krb5_principal	 princ;
	krb5_principal	 sprinc;
	int		 ch;
	int		 ret;
	int		 do_tcp = 0;
	int		 do_udp = 0;
	int		 do_v4 = 0;
	int		 do_v5 = 0;
	int		 do_524 = 0;
	int		 times = 1;
	int		 use_kt = 0;
	char		 v4_ticket_file[128];
	char		*passwd = NULL;
	char		*tprinc = NULL;
	char		*tsprinc = NULL;

	progname = strrchr(argv[0], '/');
	if (progname)
		progname++;
	else
		progname = argv[0];

	while ((ch = getopt(argc, argv, "459P:S:kn:p:tuv")) != -1)
		switch (ch) {
		case '4':
			do_v4 = 1;
			break;
		case '5':
			do_v5 = 1;
			break;
		case '9':
			do_524 = 1;
			break;
		case 'P':
			free(passwd);
			passwd = strdup(optarg);
			break;
		case 'S':
			free(tsprinc);
			tsprinc = strdup(optarg);
			break;
		case 'k':
			use_kt = 1;
			break;
		case 'n':
			times = atoi(optarg);
			break;
		case 'p':
			free(tprinc);
			tprinc = strdup(optarg);
			break;
		case 't':
			do_tcp = 1;
			break;
		case 'u':
			do_udp = 1;
			break;
		case 'v':
			verbose++;
			break;
		default:
			usage();
		}
	argc -= optind;
	argv += optind;

	/* Check sanity */

	if (passwd && use_kt) {
		fprintf(stderr, "Cannot use both passwd and keytab.\n");
		exit(1);
	}

#ifdef HAVE_KRB4
	if (do_v4 && use_kt) {
		fprintf(stderr, "Cannot use keytab with Kerberos IV.\n");
		exit(1);
	}
#endif

#ifndef HAVE_KRB4
	if (do_v4 || do_524) {
		fprintf(stderr, "Kerberos IV unsupported in this "
		    "implementation.\n");
		exit(1);
	}
#endif

	/* Fill in default values */

	if (!tprinc)
		tprinc = strdup(PING_PRINC);
	if (!tsprinc)
		tsprinc = strdup(PING_SPRINC);
	if (!use_kt && !passwd)
		passwd = strdup(PING_PASSWD);
	if (!use_kt && !*passwd) {    /* on empty passwds we prompt for it */
		passwd = getpass("Password:");
	}

	if (!do_tcp && !do_udp)
		do_tcp = do_udp = 1;
	if (!do_v4 && !do_v5 && !do_524)
		do_v5 = do_524 = 1;
	if (do_524)
		do_v5 = 1;

	K5BAIL(krb5_init_context(&ctx));
	K5BAIL(krb5_parse_name(ctx, tprinc, &princ));
	K5BAIL(krb5_parse_name(ctx, tsprinc, &sprinc));

	free(tprinc);
	free(tsprinc);
	krb5_unparse_name(ctx, princ, &tprinc);
	krb5_unparse_name(ctx, sprinc, &tsprinc);

#ifdef HAVE_KRB4
	sprintf(v4_ticket_file, "/tmp/k5ping_tkt4_%d_%d", getpid(), getuid());
	k_set_default_cache_k4(ctx, v4_ticket_file);
#endif

	VERBOSE(1, (stderr, "princ: %s\nsprinc: %s\n", tprinc, tsprinc));

	while (times-- > 0) {
		int	i;

		ret = 0;
		for (i=0; argv[i]; i++) {
			if (do_v5 && do_tcp && k5ping(ctx, argv[i], SOCK_STREAM,
			    princ, use_kt, passwd, sprinc)) {
				ret++;
				continue;
			}
			if (do_v5 && do_udp && k5ping(ctx, argv[i], SOCK_DGRAM,
			    princ, use_kt, passwd, sprinc)) {
				ret++;
				continue;
			}
#ifdef HAVE_KRB4
			if (do_524 && k524ping(ctx, argv[i], tsprinc)) {
				ret++;
				continue;
			}
			if (do_v4 && k4ping(ctx, argv[i], princ, passwd,
			    sprinc)) {
				ret++;
				continue;
			}
#endif
			if (times == 0)
				printf("k5ping(%s): successful\n", argv[i]);
		}
	}

done:
	if (croakstr[0])
		fprintf(stderr, "FATAL: %s\n", croakstr);

	exit(ret);
}
