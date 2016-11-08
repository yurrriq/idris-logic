IDRIS ?= idris
LIB   := logic
TEST  := test

# N.B. The ordering in DEPS is significant.
DEPS     := yurrriq/idris-bifunctors
DEPS_DIR ?= deps

.PHONY: install-deps lib clean check clobber install rebuild test docs docs-clean

all: lib README.md

install-deps: $(DEPS_DIR)

$(DEPS_DIR):
	mkdir -p $@
	./bin/install-deps.sh $@ $(DEPS)

lib:
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

clean:
	${IDRIS} --clean ${LIB}.ipkg
	find . -name "*~" -delete

check: clobber
	${IDRIS} --checkpkg ${LIB}.ipkg

clobber: clean docs-clean
	find . -name "*.ibc" -delete

install:
	${IDRIS} --install ${LIB}.ipkg

rebuild: clean lib

test: clean install
	${IDRIS} --testpkg ${TEST}.ipkg

docs: build docs-clean
	${IDRIS} --mkdoc ${LIB}.ipkg \
	&& rm -rf docs >/dev/null \
	&& mv ${LIB}_doc docs

docs-clean:
	rm -rf ${LIB}_doc docs >/dev/null

README.md: src/Data/Logic.lidr src/pandoc-minted.py
	pandoc --filter $(word 2,$^) \
	-f markdown+lhs+tex_math_single_backslash \
	-t markdown_github \
	-o $@ $<
