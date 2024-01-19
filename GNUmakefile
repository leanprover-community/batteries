TESTS = $(wildcard test/*.lean)

# Ensure that panics actually cause the tests to fail
export LEAN_ABORT_ON_PANIC=1

.PHONY: all build test lint

all: build test

build:
	lake build

test: $(addsuffix .run, $(TESTS))

test/%.run: build
	lake env lean test/$*

lint: build
	./.lake/build/bin/runLinter
