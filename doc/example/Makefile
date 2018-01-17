
KLEE_INCLUDE=~/proj/klee/include/

CFLAGS=-DKLEE_VERIFICATION -I ${KLEE_INCLUDE} -g
KLEE_FLAGS=--libc=uclibc --posix-runtime --dump-call-traces --max-memory=12000 --dump-call-trace-prefixes

ring-stub.bc: ring-stub.c vigor.h
	clang ring-stub.c -emit-llvm -c ${CFLAGS} -o ring-stub.bc

loop-stub.bc: loop-model.c loop-model.h user-params.h ring.h
	clang loop-model.c -emit-llvm -c ${CFLAGS} -o loop-stub.bc

ex-linv.bc: loop-inv.c packet.h vigor.h
	clang loop-inv.c -emit-llvm -c ${CFLAGS} -o ex-linv.bc

ex-model.bc: model.c packet.h ring-stub.bc loop-stub.bc vigor.h user-params.h
	clang model.c -emit-llvm -c ${CFLAGS} -o ex-mo.bc
	llvm-link ex-mo.bc ring-stub.bc loop-stub.bc -o ex-model.bc

verify-loop-inv: ex-linv.bc
	klee ${KLEE_FLAGS} ex-linv.bc

verify-model-symbolically: ex-model.bc
	klee ${KLEE_FLAGS} ex-model.bc

validate-model:
	corebuild -I validator -no-hygiene -lib dynlink ring_fspec.cmo
	./validator/test_all.sh ./klee-last ggg . _build/ring_fspec.cmo

verify-ring: ring.c ring.h user-params.h
	verifast -I ../../../nat ring.c

verify-model: verify-model-symbolically validate-model verify-ring

clean:
	rm *.bc klee-* _build ggg -rf
