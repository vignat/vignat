#pragma once

// This file isn't in the Ruby repo... so let's use it to declare the stuff Ruby doesn't declare

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#pragma GCC diagnostic ignored "-fpermissive"

#define TRUE 1

#define FALSE 0

#define LONG_LONG long long

#define SIZEOF_VOIDP 8

#define SIZEOF_LONG 8

#define SIZEOF_LONG_LONG 8

// a custom memcpy, really?
#define MEMCPY(p1,p2,type,n) memcpy((p1), (p2), sizeof(type)*(size_t)(n))

#define RUBY_SYMBOL_EXPORT_BEGIN
#define RUBY_SYMBOL_EXPORT_END
