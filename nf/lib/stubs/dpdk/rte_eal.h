#pragma once


static inline int
rte_eal_init(int argc, char **argv)
{
	int index = 0;

	// Skip args until --
	while (strcmp("--", argv[index])) {
		index++;
	}

	return index;
}
