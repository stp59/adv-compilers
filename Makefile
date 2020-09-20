.PHONY: all build clean

all: build

default: build

build:
	@dune build bin/main.exe
	@cp _build/default/bin/main.exe bril-opt

clean:
	@dune clean

test-contrived: build
	@turnt test-contrived/*.bril

test-tdce: build
	@turnt test-tdce/*.bril

test-lvn: build
	@turnt test-lvn/*.bril

test: build
	@turnt benchmarks/*.bril