
KLEE_INCLUDE=~/proj/klee/include/

CFLAGS=-DKLEE_VERIFICATION -I ${KLEE_INCLUDE} -g
KLEE_FLAGS=--libc=uclibc --posix-runtime --dump-call-traces --max-memory=12000 --dump-call-trace-prefixes

ring-stub.bc: ring-stub.c vigor.h
	clang ring-stub.c -emit-llvm -c ${CFLAGS} -o ring-stub.bc

loop-stub.bc: loop-model.c loop-model.h
	clang loop-model.c -emit-llvm -c ${CFLAGS} -o loop-stub.bc

ex-linv.bc: loop-inv.c packet.h vigor.h
	clang loop-inv.c -emit-llvm -c ${CFLAGS} -o ex-linv.bc

ex-model.bc: model.c packet.h ring-stub.bc loop-stub.bc vigor.h
	clang model.c -emit-llvm -c ${CFLAGS} -o ex-mo.bc
	llvm-link ex-mo.bc ring-stub.bc loop-stub.bc -o ex-model.bc

verify-model: ex-model.bc
	klee ${KLEE_FLAGS} ex-model.bc

verify-loop-inv: ex-linv.bc
	klee ${KLEE_FLAGS} ex-linv.bc

clean:
	rm *.bc klee-* -rf
