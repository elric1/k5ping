/*  */

/*-
 * Copyright 2009  Morgan Stanley and Co. Incorporated
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

/* begin - for solaris 2.5.1 */
#include <netinet/in.h>
/* XXXrcd: this next one is _horrible_, but seems to work... */
#define inline
/* end   - for solaris 2.5.1 */

#include <k5-int.h>
#include <kerberosIV/krb.h>
#include <kapi.h>

/*
 * Prototypes.
 */

static void	usage(void);
static void	fail_msg(const char *, int, const char *, const char *);
static void	parse_kdc(const char *host);
static int	kvno4(k_context, const char *, krb5_principal);
static int	kvno5(k_context, const char *, int, krb5_principal,
		      krb5_principal);
static int	k5ping(k_context, const char *, int, krb5_principal,
		       const char *, krb5_principal);
static int	k4ping(k_context, const char *, krb5_principal, const char *,
		       krb5_principal);
static int	k524ping(k_context, const char *, const char *);

/*
 * Macros.
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

/*
 * We over-ride the krb5_locate_kdc() function from -lkrb5 so that
 * we control both the horizontal and the verticle when it comes to
 * choosing which KDCs will be used.  As of MIT Kerberos 1.3, this
 * function takes socktype and family arguments.
 */

krb5_error_code
krb5_locate_kdc(krb5_context context, const krb5_data *realm,
                struct addrlist *addrlist,
                int get_masters, int socktype, int family)
{
	krb5_error_code	ret;
	struct addrlist	al = ADDRLIST_INIT;

	*addrlist = al;

	VERBOSE(3, (stderr, "krb5_locate_kdc(context, \"%s\", addrlist, "
	    "%d, %d, %d ) called\n", realm->data, get_masters, socktype,
	    family));

	/*
	 * krb524d is always a udp service, so we if we are doing 524,
	 * then we hardwire to SOCK_DGRAM.
	 */

	if ((!force_udp && socktype != current_socktype) ||
	    ( force_udp && socktype != SOCK_DGRAM))
		return KRB5_REALM_CANT_RESOLVE;

	VERBOSE(3, (stderr, "adding %s to the list...\n", current_kdc));
	ret = krb5int_add_host_to_list(&al, current_kdc, current_port,
	    current_secport, socktype, family);

	VERBOSE(3, (stderr, "krb5int_add_host_to_list returns %d\n", ret));

	/* XXXrcd: should free space on errors, apparently */
	if (ret)
		return ret;

	VERBOSE(4, (stderr, "we have %d addresses\n", al.naddrs));

	if (!al.naddrs)
		return KRB5_REALM_CANT_RESOLVE;

	*addrlist = al;
	return 0;
}

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

static int
kvno4(k_context ctx, const char *host, krb5_principal sprinc)
{
	krb5_context	kctx;
	krb5_error_code	kerr;
	KTEXT_ST	req;
	CREDENTIALS	creds;
	int		err = 0;
	char		name[ANAME_SZ];
	char		instance[INST_SZ];
	char		realm[REALM_SZ];

	VERBOSE(1, (stderr, "initiating kvno4/udp ping to %s\n", host));

	kctx = k_get_krb5_context(ctx);
	kerr = krb5_524_conv_principal(kctx, sprinc, name, instance, realm);
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

static int
kvno5(k_context ctx, const char *host, int socktype, krb5_principal princ,
    krb5_principal sprinc)
{
	krb5_context	 k5ctx;
	krb5_error_code	 kerr = 0;
	krb5_creds	 increds;
	krb5_creds	*outcreds = NULL;
	krb5_ccache	 ccache = NULL;
	krb5_ticket	*ticket = NULL;

	VERBOSE(1, (stderr, "initiating kvno5/%s ping to %s\n",
	    socktype == SOCK_DGRAM ? "udp" : "tcp", host));
	k5ctx = k_get_krb5_context(ctx);

	kerr = krb5_cc_default(k5ctx, &ccache);
	if (kerr)
		goto bail;

	memset(&increds, 0x0, sizeof(increds));
	increds.client = princ;
	increds.server = sprinc;
	kerr = krb5_get_credentials(k5ctx, 0, ccache, &increds, &outcreds);
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
		krb5_free_ticket(k5ctx, ticket);
	if (outcreds)
		krb5_free_creds(k5ctx, outcreds);

	krb5_cc_close(k5ctx, ccache);
	return kerr;
}

static int
k5ping(k_context ctx, const char *host, int socktype, krb5_principal princ,
    const char *passwd, krb5_principal sprinc)
{
	krb5_error_code	 kerr;
	int		 err;
	char		*tprinc;
	char		*tmp;

	VERBOSE(1, (stderr, "initiating kerberos5/%s ping to %s\n",
	    socktype == SOCK_DGRAM ? "udp" : "tcp", host));

	parse_kdc(host);
	current_socktype = socktype;

	kerr = krb5_unparse_name(k_get_krb5_context(ctx), princ, &tprinc);
	if (kerr) {
		fail_msg("kerberos5", socktype, host, error_message(kerr));
		return kerr;
	}
	err = k_login(ctx, tprinc, passwd, NULL, 3600, 0, K_OPT_NONE);
	krb5_free_unparsed_name(k_get_krb5_context(ctx), tprinc);
	if (err) {
		fail_msg("kerberos5", socktype, host, k_error_string(ctx));
		return err;
	}
	return kvno5(ctx, host, socktype, princ, sprinc);
}

static int
k4ping(k_context ctx, const char *host, krb5_principal princ,
    const char *passwd, krb5_principal sprinc)
{
	krb5_context	kctx;
	krb5_error_code	kerr;
	int		ret;
	char		name[ANAME_SZ];
	char		instance[INST_SZ];
	char		realm[REALM_SZ];

	VERBOSE(1, (stderr, "initiating kerberos4/udp ping to %s\n", host));
	parse_kdc(host);
	kctx = k_get_krb5_context(ctx);
	kerr = krb5_524_conv_principal(kctx, princ, name, instance, realm);
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
	k_logout_k4(ctx, NULL, K_OPT_NONE);

bail:
	return ret;
}

static int
k524ping(k_context ctx, const char *host, const char *tsprinc)
{
	krb5_context	 kctx;
	krb5_principal	 sprinc = NULL;
	CREDENTIALS	 v4creds;
	int		 kret;

	VERBOSE(1, (stderr, "initiating kerberos524/udp ping to %s\n", host));

	parse_kdc(host);

	/*
	 * Apparently, k_convert_creds_524() seems to corrupt
	 * sprinc...
	 */

	kctx = k_get_krb5_context(ctx);
	kret = krb5_parse_name(kctx, tsprinc, &sprinc);
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
	krb5_free_principal(kctx, sprinc);
#endif
	return kret;
}

int
main(int argc, char **argv)
{
	k_context	 ctx;
	krb5_context	 kctx;
	krb5_principal	 princ;
	krb5_principal	 sprinc;
	krb5_error_code	 kret;
	int		 ch;
	int		 ret;
	int		 do_tcp = 0;
	int		 do_udp = 0;
	int		 do_v4 = 0;
	int		 do_v5 = 0;
	int		 do_524 = 0;
	int		 times = 1;
	char		 v4_ticket_file[128];
	char		*passwd = NULL;
	char		*tprinc = NULL;
	char		*tsprinc = NULL;

	progname = strrchr(argv[0], '/');
	if (progname)
		progname++;
	else
		progname = argv[0];

	while ((ch = getopt(argc, argv, "459P:S:n:p:tuv")) != -1)
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

	/* Fill in default values */

	if (!tprinc)
		tprinc = strdup(PING_PRINC);
	if (!tsprinc)
		tsprinc = strdup(PING_SPRINC);
	if (!passwd)
		passwd = strdup(PING_PASSWD);
	if (!*passwd) {	/* on empty passwds we prompt for it */
		passwd = getpass("Password:");
	}

	if (!do_tcp && !do_udp)
		do_tcp = do_udp = 1;
	if (!do_v4 && !do_v5 && !do_524)
		do_v5 = do_524 = 1;
	if (do_524)
		do_v5 = 1;

	if (k_init_ctx(&ctx, progname, K_OPT_NONE)) {
		fprintf(stderr, "k5ping ERROR - unable to initalize kapi "
		    "context\n");
		exit(1);
	}

	sprintf(v4_ticket_file, "/tmp/k5ping_tkt4_%d_%d", getpid(), getuid());

	k_set_default_cache(ctx, "MEMORY:k5ping");
	k_set_default_cache_k4(ctx, v4_ticket_file);

	/* XXXrcd: put error checking here... */
	kctx = k_get_krb5_context(ctx);
	kret = krb5_parse_name(kctx, tprinc, &princ);
	if (kret) {
		fprintf(stderr, "malformed princ %s: %s\n", tprinc,
		    error_message(kret));
		exit(127);
	}
	kret = krb5_parse_name(kctx, tsprinc, &sprinc);
	if (kret) {
		fprintf(stderr, "malformed princ %s: %s\n", tsprinc,
		    error_message(kret));
		exit(127);
	}
	free(tprinc);
	free(tsprinc);
	krb5_unparse_name(kctx, princ, &tprinc);
	krb5_unparse_name(kctx, sprinc, &tsprinc);

	VERBOSE(1, (stderr, "princ: %s\nsprinc: %s\n", tprinc, tsprinc));

	while (times-- > 0) {
		int	i;

		ret = 0;
		for (i=0; argv[i]; i++) {
			if (do_v5 && do_tcp && k5ping(ctx, argv[i], SOCK_STREAM,
			    princ, passwd, sprinc)) {
				ret++;
				continue;
			}
			if (do_v5 && do_udp && k5ping(ctx, argv[i], SOCK_DGRAM,
			    princ, passwd, sprinc)) {
				ret++;
				continue;
			}
			if (do_524 && k524ping(ctx, argv[i], tsprinc)) {
				ret++;
				continue;
			}
			if (do_v4 && k4ping(ctx, argv[i], princ, passwd,
			    sprinc)) {
				ret++;
				continue;
			}
			if (times == 0)
				printf("k5ping(%s): successful\n", argv[i]);
		}
	}

	k_close_ctx(ctx);
	exit(ret);
}
