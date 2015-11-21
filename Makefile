.PHONY: doc showdoc build test showtest clean

default: test

Setup:
	ghc Setup.hs

dist: Setup
	./Setup configure --enable-tests

sdist: dist
	./Setup sdist

doc: dist
	./Setup haddock

showdoc: doc
	$(BROWSER) dist/doc/html/cayley-dickson/Math-CayleyDickson.html

build: dist
	./Setup build

test: build
	./Setup test

showtest: build
	./dist/build/test/test

clean:
	git clean -fdx
