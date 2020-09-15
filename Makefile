.PHONY: all build clean

all: build

default: build

build:
	@dune build bin/main.exe
	@cp _build/default/bin/main.exe test-contrived/contrived.exe

clean:
	@dune clean

test:
	turnt test-contrived/*.bril