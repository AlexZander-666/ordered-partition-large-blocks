# Ordered set partitions from the first marked block through the first cubic row

Let O(n,j;t) count ordered set partitions of the labels [n] by the number of blocks of size at least j. Every integer threshold j≥2 and every adjacent pair of ranks n,n+1 with j≤n<3j have strictly interlacing negative roots. For the uniform distribution on these partitions, all positive-order binomial moments of the count of large blocks increase strictly from their first appearance onward, at arbitrary ranks.

## Exact coverage

* When n+1<2j, both rows are linear and the old root is strictly to the left of the new root.
* At n+1=2j the old linear root lies strictly between the two new roots.
* When 2j≤n and n+1<3j, the two old roots and two new roots alternate in the order old, new, old, new.
* At n+1=3j the three new roots bracket the two old roots in the order new, old, new, old, new. The quadratic and cubic conclusions give complete real factorizations and root multisets.
* If h≥1 and hj≤n+1, the expected value of binom(K,h) increases strictly, where K is the number of large blocks. Before rank hj the numerator vanishes and it is positive at rank hj. This remains true for n≥3j.

The top declarations are `OrderedPartitions.original_initial_chambers`, `OrderedPartitions.original_quadratic_chamber`, and `OrderedPartitions.Kernel.original_binomial_moment_from_entry`. The primitive sample space in `FirstJump.lean` consists of surjections from Fin n to the ordered set Fin b. Its fibres are unordered sets. The rank generating polynomial and its coefficients are in `FirstJumpRows.lean`. The identities for the true marked moments are in `MarkedSeries.lean`. The large-j estimates use a proved geometric error bound for the ordinary ordered Bell numbers. The finite verification covers all 1,224 quadratic pairs for 2≤j≤49, including 48 quadratic-to-cubic jumps, with exact integer kernel reductions. The general real-root and interlacing question beyond the first cubic row remains open. [Original problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees)

## Reproduce

Use the Lean version in `lean-toolchain` and the nine dependency commits in `lake-manifest.json`. On a machine without these dependencies, prepare a second copy of the package with `lake update` and `lake exe cache get`, and confirm that its dependency revisions match the original manifest. Then extract the frozen source again and run

```sh
python3 verify.py /absolute/path/to/the/prepared/.lake/packages 2
```

The optional final argument sets concurrent per-module replays. The verifier requires a source tree without a .lake directory. It verifies source hashes, local imports, dependency commits and tracked-file cleanliness, rejects proof placeholders and extra axiom declarations, and runs a warning-as-error build. No project object files are reused. It checks the axiom reports, including the 48 finite cutoff checks, and separately replays every local module with leanchecker. Each recorded object digest belongs to this build. The mathematical assertions are unconditional in the indicated integer ranges. The reconstruction uses cached external library objects.
