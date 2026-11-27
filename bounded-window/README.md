# Full interlacing windows for ordered set partitions at bounded ratio

Bowen Zuo, East China University of Science and Technology.

For each fixed ratio cap C≥1 there is J(C) such that whenever j≥J(C)
and j≤n≤Cj, the complete original root arrays at n and n+h strictly
interlace for every h from 1 through j. All roots are simple and negative.
The period comparison separates the two far-left roots that diverge at
an integral ratio.

- [Paper](paper/main.pdf) · [Release](https://github.com/AlexZander-666/ordered-partition-large-blocks/releases/tag/bounded-window-v1.0.0)
- [Lean source and reproduction commands](formal/README.md)
- [Formal statement map](verification/STATEMENT-MAP.md) · [Spark audit](verification/FINAL-AUDIT.md) · [Published adjacent-row theorem](https://doi.org/10.5281/zenodo.24570914)

Run `sha256sum -c SHA256SUMS` here. For the manuscript, extract
`paper/arxiv-source.zip` and run `python3 -B reproduce.py --output main.pdf
--log build.log` from the extracted directory. TeX Live 2026 and Latin
Modern fonts reproduce the recorded PDF bytes.

The locked Lean project enters through `OrderedPartitions.HardRodWindowVerified`.
It starts from the original ordered surjection rows. The source-cold Spark
run strictly rebuilt all 82 local modules and replayed 82 separate Lean
kernel processes, with 212 source and eight targeted axiom reports.
Apache-2.0 covers original proof and verification code. The manuscript and
TeX remain copyright Bowen Zuo.
