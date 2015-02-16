run: bench
	./bench

report: report.tmpl stats.sh
	. ./stats.sh; echo "$$(eval "echo \"$$(cat report.tmpl)\"")"

stats.sh: runs.txt
	awk '{ tot=0; sqtot=0; for (i=1; i<=NF; i++) {tot += $$i; sqtot += $$i*$$i;}; sigma = sqrt((sqtot - tot*tot/NF)/(NF-1)); printf "r%d=\"%6.1f-:-%6.1f\"\n", NR, tot/NF, sigma; }' runs.txt > stats.sh

runs.txt: bench
	rm -f runs.txt & touch runs.txt
	rm -f tmp.txt
	for i in `seq 1 50`; do	./bench o | paste runs.txt - > tmp.txt && cp tmp.txt runs.txt; done
	rm tmp.txt

bench: engine.cpp ../coq/map.c data.c operations.c
	g++ engine.cpp -std=c++11 -I/usr/include/glib-2.0 -I /usr/lib/x86_64-linux-gnu/glib-2.0/include -lglib-2.0 -L/lib/x86_64-linux-gnu/ -o bench

operations.c: generate.el
	emacs -Q -batch operations.c -l generate.el --eval="(gen-seq-matrix 5)" -f save-buffer

data.c: generate.el
	emacs -Q -batch data.c -l generate.el --eval="(gen-key-set 50)" -f save-buffer
