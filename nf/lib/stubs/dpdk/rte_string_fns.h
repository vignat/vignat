#pragma once

// we include the actual function implementation in the Makefile
// here it's just the header
int
rte_strsplit(char *string, int stringlen, char **tokens, int maxtokens, char delim);
