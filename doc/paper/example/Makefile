
KLEE_INCLUDE=~/proj/klee/include/

ring-stub.bc: ring-stub.c vigor.h
	clang ring-stub.c -emit-llvm -g -c -I ${KLEE_INCLUDE} -o ring-stub.bc

ex-linv.bc: loop-inv.c packet.h vigor.h
	clang loop-inv.c -emit-llvm -g -c -I ${KLEE_INCLUDE} -o ex-linv.bc

ex-model.bc: model.c packet.h ring-stub.bc vigor.h
	clang model.c -emit-llvm -g -c -I ${KLEE_INCLUDE} -o ex-mo.bc
	llvm-link ex-mo.bc ring-stub.bc -o ex-model.bc

verify-model: ex-model.bc
	klee ex-model.bc

verify-loop-inv: ex-linv.bc
	klee ex-linv.bc

clean:
	rm *.bc klee-* -rf
