# Publication notes for the six-page edition

The PDF, LaTeX archive and verified Lean archive use the exact reviewed bytes. The companion materials are available at [the release `bounded-ratio-v1.0.0`](https://github.com/AlexZander-666/ordered-partition-large-blocks/releases/tag/bounded-ratio-v1.0.0), which fixes the 76-module development and the two exception theorems alongside the main result.

## References and proof guide

- Fang's version 1, Theorem 1 treats the fixed threshold 4 for unordered set partitions. [Fang, version 1](https://hexagonmath.org/2611.01129v1)
- The formal two-size ordered classification cited through RealRooted #2665 uses block sizes 1 and 2. [Pinned declaration source](https://github.com/PerAlexandersson/RealRooted/blob/dbf6666ea032cc741e652c91ee74b935a4d2906e/RealRooted/ExponentialRows/TwoSizeClassification.lean)
- The dynamic SymCat problem and weighted-renewal pages were consulted on 27 November 2026. [Ordered-partition question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees) · [Weighted renewal](https://www.symmetricfunctions.com/realRootedInterlacing.htm#renewal-recurrences-with-a-real-rooted-seed)
- For the integer-boundary proof, the forward difference splits as $j\,\Delta a_h=\Delta U/(j^{h-1}k_{n+1})+(U/j^{h-1})\Delta(1/k_n)$. The escape estimate is $A_0/(j\Delta)\le4(m+3)/j\to0$, and the limit polynomial has degree $\lceil x\rceil-1$ for $x>0$. These statements are used in the paper's limiting and integer-ratio arguments.

## Reproduce the reviewed bytes

The `ulimit` increase suggested in the frozen source README is optional. The independent x86_64 review successfully ran the full source build and module replays at a 16,384-descriptor limit. Start from a fresh extraction and run the verifier directly after preparing the locked external package cache.

```sh
cd formal
python3 -B verify.py /absolute/path/to/locked/.lake/packages 2
```

The 76 Lean modules are rebuilt from source and replayed in separate processes using the same Lean kernel implementation. The run reuses compiled external libraries at nine locked Git revisions. The Linux ARM64 author-side build and the independent x86_64 review agreed on the object digests of all 76 modules.

From the release directory, `python3 -B paper/reproduce.py` builds the TeX PDF. A local TeX Live 2026 run reproduced the reviewed six-page PDF in two independent build directories with two passes each. The independent mathematical review checked PDF and LaTeX content correspondence and hit a TeX installation issue before it could rebuild the PDF.
