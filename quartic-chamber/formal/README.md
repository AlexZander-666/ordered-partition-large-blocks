# Strict interlacing through the first quartic row

For every integer cutoff j≥2 and every rank 3j≤n<4j, the original ordered-set-partition enumerators at ranks n and n+1 have simple, strictly negative interlacing roots. A block is marked when its size is at least j. At n+1=4j the new smallest root lies to the left of the three old roots. The combined statement covers every adjacent pair with j≤n<4j.

The public declarations are OrderedPartitions.original_cubic_chamber and OrderedPartitions.original_through_first_quartic in OrderedPartitions/CubicChamberVerified.lean. See OrderedPartitions/CubicQuarticOrder.lean for the complete root and order predicates, whose finite lists give the full factorizations.

## Reproduce

Use Lean 4.33.1 under the included toolchain pin, Python 3.10 or later, and a directory of clean external Lake packages matching lake-manifest.json, including compiled Mathlib dependencies. In a fresh extraction run `python3 verify.py /absolute/path/to/locked/packages 4`. Four is the number of per-module replay workers. The verifier rejects existing project build artifacts, verifies dependency revisions and source hashes, checks forbidden proof constructs, builds the top with warnings as errors, prints transitive axioms, and rechecks each local module with leanchecker. The external dependency binaries may be prepared separately with Lake and the official Mathlib cache. All local theorem objects are rebuilt from the included Lean source.

The source contains the positive-renewal estimates for the true marked counts, all 777 rational box checks, all 62 finite-cutoff cases, the interval and factorization arguments, and the earlier initial-chamber statements. This archive contains only the proof sources, formal dependency lock and reproduction files.
