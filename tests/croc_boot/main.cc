#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

#include "croc_soc.cc"

int main(int argc, const char *argv[]) {
	if (argc != 2)
		exit(1);

	int sock = socket(AF_UNIX, SOCK_STREAM, 0);
	if (sock == -1) {
		perror("socket");
		exit(2);
	}

	struct sockaddr_un name;
	memset(&name, 0, sizeof(name));
	name.sun_family = AF_UNIX;
	if (strlen(argv[1]) >= sizeof(name.sun_path)) {
		fprintf(stderr, "bad length\n");
		exit(3);
	}
	strcpy(name.sun_path, argv[1]);

	int ret = bind(sock, (struct sockaddr *) &name, sizeof(name));
	if (ret == -1) {
		perror("bind");
		exit(4);
	}

	int pid = fork();
	if (pid > 0)
		exit(0);
	if (pid < 0) {
		perror("fork");
		exit(5);
	}

	ret = listen(sock, 0);
	if (ret == -1) {
		perror("listen");
		exit(6);
	}

	int fd = accept(sock, NULL, NULL);
	if (fd == -1) {
		perror("accept");
		exit(7);
	}

	cxxrtl_design::p_croc__soc top;
	top.p_irq0__i.set(false);
	top.p_test__enable__i.set(false);
	top.p_rst__ni.set(false);
	top.p_clk__i.set(false);
	top.step();
	top.p_clk__i.set(true);
	top.step();
	top.p_rst__ni.set(true);
	top.step();
	for (int i = 0; i < 10; i++) {
		top.p_clk__i.set(false);
		top.step();
		top.p_clk__i.set(true);
		top.step();
	}

	auto& fetch_en = top.p_i__croc_2e_i__soc__ctrl_2e_u__fetchen_2e_q;
	auto& mem = top.memory_p_i__croc_2e_gen__sram__bank_5b_0_5d__2e_i__sram_2e_sram;

	fetch_en.curr.set(1);
	fetch_en.next.set(1);
	mem[0x80].set(0x10500073u); // wfi
	mem[0x84].set(0xffdff06fu); // jal x0, -4

	top.p_clk__i.set(false);
	top.step();

	while (1) {
		char c;
		if (read(fd, &c, 1) != 1) {
			perror("read");
			exit(8);
		}

		switch (c) {
		case 'B':
			fprintf(stderr, "blink on\n");
			continue;
		case 'b':
			fprintf(stderr, "blink off\n");
			continue;
		case 'R':
			c = (top.p_jtag__tdo__o.get<int>() & 1) ? '1' : '0';
			write(fd, &c, 1);
			continue;
		case 'Q':
			exit(0);
		case '0' ... '7': // tck tms tdi
			c -= '0';
			top.p_jtag__tck__i.set((c & 4) != 0);
			top.step();
			top.p_jtag__tdi__i.set((c & 1) != 0);
			top.p_jtag__tms__i.set((c & 2) != 0);
			break;
		case 'r' ... 'u': // trst srst
			c -= 'r';
			//top.p_srst__pad__i.set((c & 1) != 0);
			top.p_jtag__trst__ni.set((c & 2) == 0);
			break;
		default:
			fprintf(stderr, "ignoring '%c'\n", c);
			continue;
		}

		top.step();

		top.p_clk__i.set(true);
		top.step();
		top.p_clk__i.set(false);
		top.step();
	}
}
