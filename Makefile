.PHONY: all build clean

all: build

default: build

build:
	@dune build bin/main.exe