#pragma once

int rte_errno;

static inline const char*
rte_strerror(int errnum)
{
	return "stub error";
}
