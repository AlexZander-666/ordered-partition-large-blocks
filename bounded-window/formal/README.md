# Full-window interlacing for ordered labelled partitions at bounded ratio

For every real C there exists a natural K such that whenever j≥K and j≤n≤Cj, each pair of original rows at n and n+h strictly interlaces for all integral 1≤h≤j. When rank rises the new extreme root lies on the left; in both degree cases the new rightmost root lies on the right. RootArray represents all strictly negative roots through the exact degree.

The main public entry is OrderedPartitions.original_full_window_bounded_ratio, with a separate original_full_period_bounded_ratio statement. The proof transfers the unit hard-rod separation, controls the two roots tending to minus infinity at an integral entrance using two actual leading coefficients, and composes adjacent rightward root motion. The threshold is qualitative. This source package contains the actual local import closure and the locked external package manifest.

To reproduce from a fresh source extraction with the matching external Mathlib packages and the toolchain in lean-toolchain, run

    python3 verify.py /path/to/locked-external-lake-packages 2

The argument is a path to the installed external dependencies checked against the lock. The verifier rejects existing project build objects, invokes a warning-as-error Lake build and separately runs leanchecker on every local module and checks all printed axiom claims.
