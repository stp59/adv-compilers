.PHONY: all build clean

all: build

default: build

build:
	@dune build bin/main.exe

clean:
	@dune clean

test:
	turnt test-contrived/*.bril