TESTS = $(wildcard test/*.lean)

# Ensure that panics actually cause the tests to fail
export LEAN_ABORT_ON_PANIC=1

.PHONY: all build test lint

all: build test

build:
	lake build

# Find all .lean files in test and subdirectories, replace .lean with .run
TESTS := $(shell find test -type f -name '*.lean' | sed 's/\.lean$$/.run/')

test: $(TESTS)

%.run: build
	lake env lean $(@:.run=.lean)

lint: build
	./.lake/build/bin/runLinter
