#pragma once

// Our version of clang doesn't support SSSE3...
// TODO try updating it? not sure how KLEE will enjoy that...

#include <emmintrin.h>
inline __m128i _mm_alignr_epi8(__m128i a, __m128i b, int n) { return (__m128i) {0, 0}; }
