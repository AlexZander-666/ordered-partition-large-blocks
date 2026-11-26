# Interlacing of ordered-partition rows below a fixed rank ratio

`OrderedPartitions.original_interlacing_bounded_ratio` proves that for every fixed real cap $C$, there is a cutoff threshold $K$ such that every adjacent pair of original rows of ranks $n,n+1$ with $j\ge K$, $j\le n$ and $n\le Cj$ has the strict root order. Each row counts every ordered partition of the labeled set, with a mark for each block of size at least $j$. The conclusion describes all roots, including simplicity, negativity and the degree-increasing case. The cutoff promised by the theorem may depend on $C$.

`OrderedPartitions.finite_exceptional_rows` shows that for a fixed cap there are finitely many exceptions among threshold and rank pairs with $2\le j\le n$. `OrderedPartitions.exceptional_ratio_tendsto` shows that the ratios of any pairwise distinct sequence of exceptions tend to positive infinity.

## Files

The source entry is `OrderedPartitions/HardRodExceptions.lean`. The principal theorem is in `OrderedPartitions/HardRodBoundedRatio.lean`. `HardRodRightBrackets.lean` defines `OrderedPair`, and the indexed root arrays are in `InterlacingStep.lean`. `LastBlockRow.lean` proves the recurrence from the actual labeled objects. The sources from `HardRodWindowPoly.lean` through `HardRodEntryPair.lean` connect the limit polynomials, the degree boundaries and the affine readout to the original rows.

`lean-toolchain` pins Lean 4.33.1. `lake-manifest.json` pins Mathlib and eight other external Git dependencies. `modules.txt` orders the complete local source closure, and `SOURCE-SHA256SUMS` fixes its bytes along with the verification scripts and lock. `audit-names.txt` lists the principal declarations checked again from the entry module.

## Reproduce

Use Python 3.10 or later and prepare a separate copy of the locked external Lake package checkouts with their compiled libraries. For a machine starting without dependencies, copy the included `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` to a preparation directory, then use `lake exe cache get` there. The verifier checks the actual Git commits and tracked-source cleanliness. Take the packages path from the preparation directory.

From a fresh extraction of the source ZIP, run:

```sh
ulimit -n 65536
python3 -B verify.py /absolute/path/to/locked/.lake/packages 2
```

The optional final number is the build and replay worker bound, from one to four. `verify.py` checks the lexical proof scan, source inventory and version pins. It starts with no project objects, performs `lake --no-ansi --wfail build +OrderedPartitions.HardRodExceptions`, cross-checks Lean's resolved local imports, reviews all source axiom reports plus the targeted declarations, and launches a separate `lake env leanchecker --verbose` process for each local module. The report records each source and object digest.
