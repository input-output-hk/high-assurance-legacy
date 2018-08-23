Building
========

The official way to build the Haskell code is via `cabal new-build`.
There is a makefile, whose default target runs `cabal new-build all`.
The makefile also contains a `clean` target, which is handy because
currently there is no `cabal new-clean`.

There is also inofficial support for `stack`, but it may be less tested
than the `cabal new-build` support.
