INTERACTIVE ?= --interactive
IDRIS2_HOME:=$(shell realpath $(PWD)/jvm-assembler/target/idris2-boot-jvm)
PATH:=$(IDRIS2_HOME)/bin:$(PATH)

test:
	@../runtests $(IDRIS2_HOME)/bin/idris2 $(INTERACTIVE) --only $(only)

clean:
	find . -name '*.ibc' | xargs rm -f
	find . -name 'output' | xargs rm -f
