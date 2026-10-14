# Specftacular

[![DOI](https://zenodo.org/badge/471054656.svg)](https://zenodo.org/badge/latestdoi/471054656)

Welcome to the Specftacular project, a re-envisioning of [QuickSpec](https://hackage.haskell.org/package/quickspec) using ECTAs.
Specftacular was called Spectacular before it moved to cfta; the DOI above is that of the original Spectacular.

Specftacular uses the ECTAs of [cfta](https://github.com/TharkunAB/cfta/tree/microcfta/cfta) and builds with GHC 9.14.1.
For Specftacular itself, check out the [specftacular/](specftacular) subdirectory!
To see it in action, run `cabal build` in this directory, and then run `./benchmark.sh` in `specftacular/`.

The environment variable `SPECFTACULAR_TESTS` sets the number of test cases (1000 by default, as in QuickSpec).
Fewer test cases are faster, but they let more false laws through, and the prover builds on each law that it prints.
With 100 test cases, `bench-huge-lists 7 1` prints false laws, and the rules that follow from them hide true laws such as `xs == take x xs ++ drop x xs`.

