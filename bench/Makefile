run: bench
	./bench

perfplot.png: export.csv draw.r
	rm perfplot.png
	Rscript draw.r

report: report.tmpl stats.sh
	. ./stats.sh; echo "$$(eval "echo \"$$(cat report.tmpl)\"")"

export.csv: rexport.tmpl stats.sh
	. ./stats.sh; echo "$$(eval "echo \"$$(cat rexport.tmpl)\"")" > export.csv

stats.sh: runs.txt
	awk '{ tot=0; sqtot=0; for (i=1; i<=NF; i++) {tot += $$i; sqtot += $$i*$$i;}; sigma = sqrt((sqtot - tot*tot/NF)/(NF-1)); printf "v%d=\"%6.1f\"\ne%d=\"%6.1f\"\n", NR, tot/NF, NR, sigma; }' runs.txt > stats.sh

runs.txt: bench
	rm -f runs.txt
	rm -f tmp.txt
	touch runs.txt
	for i in `seq 1 30`; do	./bench o | paste runs.txt - > tmp.txt && cp tmp.txt runs.txt; done
	rm tmp.txt

bench: engine.cpp ../vst/map/map.c data.c operations.c
	g++ engine.cpp -std=c++11 -I/usr/include/glib-2.0 -I /usr/lib/x86_64-linux-gnu/glib-2.0/include -lglib-2.0 -L/lib/x86_64-linux-gnu/ -o bench

operations.c: generate.el Makefile
	rm -f operations.c
	emacs -Q -batch operations.c -l generate.el --eval="(gen-seq-matrix 300)" -f save-buffer

data.c: generate.el Makefile
	rm -f data.c
	emacs -Q -batch data.c -l generate.el --eval="(gen-key-set 600)" -f save-buffer

rexport.tmpl: generate.el Makefile
	rm -f rexport.tmpl
	emacs -Q -batch rexport.tmpl -l generate.el --eval="(gen-csv-template)" -f save-buffer

