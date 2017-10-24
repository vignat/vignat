#pragma once

// Our version of clang doesn't support SSSE3...
// TODO try updating it? not sure how KLEE will enjoy that...

#include <emmintrin.h>
// TODO is this reasonable?
#define _mm_alignr_epi8(a, b, n) ((__m128i) {0, 0})
