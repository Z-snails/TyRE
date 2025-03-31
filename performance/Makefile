.PHONY: all
all: build run graph

.PHONY: build
build:
	idris2 --find-ipkg Main.idr -o bench

.PHONY: run
run:
	python3 benchmark.py

.PHONY: graph
graph:
	python3 graph_csv.py
