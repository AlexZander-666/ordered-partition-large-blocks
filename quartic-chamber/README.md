# Large blocks in ordered set partitions

This revision of the paper by Bowen Zuo proves strict adjacent interlacing for every cutoff \(j\ge2\) and lower rank \(j\le n<4j\). All roots are simple and negative, including those of the upper row at the quartic entry \(n+1=4j\). The theorem on strict increase of every positive-order factorial moment from first support is also included. Each block is nonempty and contains unordered labels. All blocks themselves are linearly ordered.

[Nine-page paper](paper/main.pdf) · [LaTeX and arithmetic certificate archive](paper/arxiv-source.zip) · [GitHub v1.1.0](https://github.com/AlexZander-666/ordered-partition-large-blocks/releases/tag/v1.1.0)

## Reproduce the paper and checks

Run `sha256sum --check SHA256SUMS` from this directory. Then run the following commands using Python 3.10 or later and TeX Live 2026. Set `PDFLATEX` to the executable path if necessary.

```sh
cd paper
python3 -B reproduce.py
python3 -B anc/verify-quadratic.py
python3 -B anc/cubic-boxes.py
python3 -B anc/cubic-finite.py
python3 -B anc/cubic-independent.py
```

The script rebuilds the PDF twice from the loose source and twice from a fresh extraction of its source ZIP. The four Python checkers run without third-party packages and use exact arithmetic for all decisions. The box reporter formats already rounded margins for display. [Build log](verification/rebuild.log) · [Arithmetic replay](verification/check-replay.log)

## Rebuild and replay Lean

The original enumeration, closed rational cells, finite cutoffs, and complete root orders are formalized. The main declarations are `OrderedPartitions.original_through_first_quartic` and `OrderedPartitions.original_cubic_chamber` in `OrderedPartitions.CubicChamberVerified`. See the [statement map](verification/STATEMENT-MAP.md), [verification report](verification/FINAL-AUDIT.md), and [reproduction guide](formal/README.md).

Use Lean 4.33.1 and a separate directory of clean, compiled external packages matching `formal/lake-manifest.json`. Run the verifier on a fresh project copy with no local build objects.

```sh
tmp=$(mktemp -d)
cp -R formal/. "$tmp/"
cp verification/audit_verify_serial.py "$tmp/"
python3 -Bu "$tmp/audit_verify_serial.py" /absolute/path/to/locked/packages 1
```

The included serial driver preserves the frozen verifier's checks and builds one local module at a time. Spark and an independent x86-64 source-cold replay each verified all 81 local modules and all 249 axiom reports. The two module-receipt tables agree exactly. [Spark cold log](verification/cold.log) · [Independent module receipts](verification/r5-x86-module-receipts.tsv) · [Review and packaging notes](verification/RELEASE-NOTES.md)

Apache-2.0 applies to the original proof and verification code. The author retains copyright in the manuscript. See [NOTICE](NOTICE).
