.PHONY: all
all: build run graph

Staging/ILexGenerated.idr: Staging/ILex.idr
	./Staging/gen.sh

.PHONY: build
build: Staging/ILexGenerated.idr
	idris2 --find-ipkg Main.idr -o bench

.PHONY: run
run:
	python3 benchmark.py

.PHONY: graph
graph:
	python3 graph_csv.py

.PHONY: exe
exe: build
	cp build/exec/bench_app/bench.ss build/exec/bench_app/libidris2_support.so build/
	compile-chez-program --optimize-level 3 build/bench.ss
