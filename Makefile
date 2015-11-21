.PHONY: doc showdoc test clean

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

test: dist
	./Setup build
	./Setup test

clean:
	git clean -fdx
