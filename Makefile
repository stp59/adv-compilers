.PHONY: all build clean

all: build

default: build

build:
	@dune build bin/main.exe
	@cp _build/default/bin/main.exe bril-opt
	@echo

clean:
	@dune clean

test-contrived: build
	@turnt test-contrived/*.bril

test-tdce: build
	@turnt --diff test-tdce/*.bril

test-lvn: build
	@turnt test-lvn/*.bril

test-cp: build
	@turnt --diff test-cp/*.bril

test-to-ssa: build
	@turnt test-tossa/*.bril

test-of-ssa: build
	@turnt test-ofssa/*.bril

test: build
	@turnt benchmarks/*.bril