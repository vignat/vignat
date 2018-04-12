all: validator.byte nat_fspec.cmo bridge_fspec.cmo dmz_fspec.cmo

validator.byte: .PHONY
	corebuild -no-hygiene -use-menhir -lib dynlink -lib str validator.byte -use-ocamlfind -cflag -unsafe-string

nat_fspec.cmo: _build/nat_fspec.cmo
	cp _build/nat_fspec.cmo ./

bridge_fspec.cmo: _build/bridge_fspec.cmo
	cp _build/bridge_fspec.cmo ./

dmz_fspec.cmo: _build/dmz_fspec.cmo
	cp _build/dmz_fspec.cmo ./

_build/nat_fspec.cmo: .PHONY
	corebuild -no-hygiene -lib dynlink -lib str nat_fspec.cmo -cflag -unsafe-string

_build/bridge_fspec.cmo: .PHONY
	corebuild -no-hygiene -lib dynlinc bridge_fspec.cmo -cflag -unsafe-string

_build/dmz_fspec.cmo: .PHONY
	corebuild -no-hygiene -lib dynlinc dmz_fspec.cmo -cflag -unsafe-string

.PHONY:

clean:
	rm -rf out
	rm -rf _build
	find -iname '*.cmo' -delete
	find -iname '*.log' -delete
	rm -f validator.byte

validate-nat: clean
	./test_all.sh ../nf/vignat/klee-last out ../nf nat_fspec.cmo

validate-bridge: clean
	./test_all.sh ../nf/bridge/klee-last out ../nf bridge_fspec.cmo

validate-dmz: clean
	./test_all.sh ../nf/dmz/klee-last out ../nf dmz_fspec.cmo

# Regression test suite
test-results/%.done: regression-tests/%
	./run-test.sh $* test-results
	touch $@

check: $(patsubst regression-tests/%,test-results/%.done,$(wildcard regression-tests/*))
