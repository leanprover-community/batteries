.PHONY: all build test lint

all: build test

build:
	lake build

test:
	lake test

lint: build
	./.lake/build/bin/runLinter
