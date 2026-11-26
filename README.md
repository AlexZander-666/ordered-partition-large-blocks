# Large blocks in ordered set partitions

The bounded-ratio theorem has its own paper and 76-module Lean proof. [Bounded-ratio release](https://github.com/AlexZander-666/ordered-partition-large-blocks/releases/tag/bounded-ratio-v1.0.0)

For every block-size threshold $j\ge2$, successive counting polynomials strictly interlace from rank $j$ through the first cubic at rank $3j$. At every rank and for every positive order, the factorial moments of the number of large blocks increase strictly from their first possible occurrence onward.

An ordered set partition of $[n]$ is a list of nonempty disjoint sets covering $[n]$. Let $K$ count the sets with at least $j$ labels, and let $O_{n,j}(t)=\sum_\pi t^{K(\pi)}$. The sum gives each ordered partition weight one. At $j=2$ the rows at ranks three and four are $6+7t$ and $24+45t+6t^2$. At the old zero $-6/7$, the new row equals $-498/49$. It is positive at zero and has positive leading coefficient, so its two roots strictly straddle the old one.

## Theorems

All roots below are simple and negative. Read the letters from the most negative root to the least negative, with A for rank $n$ and B for rank $n+1$.

| Range | Root order |
| --- | --- |
| $j\le n$ and $n+1<2j$ | A B |
| $n+1=2j$ | B A B |
| $2j\le n$ and $n+1<3j$ | A B A B |
| $n+1=3j$ | B A B A B |

Under the uniform measure on ordered partitions, $\mathbb E\binom{K}{h}$ vanishes for $n<hj$ and increases strictly from $n$ to $n+1$ whenever $h\ge1$ and $n+1\ge hj$. In particular, the transition from zero to the first positive term is included. Alexandersson's question about interlacing continues beyond the first cubic. [Original statement and generating function](https://github.com/PerAlexandersson/symmetricfunctions.com/commit/265ee865f973c086bd144e53b5bf24d3cc2503f1)

[Read the paper](paper/main.pdf) or [download its LaTeX source](paper/main.tex).

## Verification

[Source-cold verification and theorem mapping](verification/verification.md)

The Lean definition encodes ordered partitions as surjections to a linearly ordered set of block positions. The main declarations are `OrderedPartitions.original_initial_chambers` and `OrderedPartitions.Kernel.original_binomial_moment_from_entry`. The first uses a recurrence from the last block, exact integer checks for small thresholds, and uniform estimates for larger thresholds. Its root counts include multiplicities. The second identifies the marked coefficients with binomial moments on the original objects.

The two exact counting checks use only the Python standard library.

```sh
python3 scripts/check_first_jump.py
python3 scripts/check_quadratic_chamber.py
```

For Lean, use the pinned toolchain and the dependency checkouts in a separate preparation directory. From a clean checkout run the following, substituting that directory's actual path. [Preparation and cold-build details](formal/README.md)

```sh
cd formal
python3 verify.py /absolute/path/to/prepared/.lake/packages 2
```

Bowen Zuo, East China University of Science and Technology. ChatGPT assisted in deriving and independently reviewing the arguments, implementing the checks and drafting the exposition. The author takes responsibility for the results.

Version 1.0.0, 27 November 2026.
