# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local NVMe project on Linux ARM64. Lean 4.33.1 built all 82 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 82 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separate copy of the existing dependency cache.

The lexical source scan passed. The 212 source reports and 8 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps the simultaneous bounded-ratio window theorem and its full-period component to the original rows.

- Source ZIP SHA-256 `bf246e653541b772a63928ec519de30b3094221deab80727d7ee95a9488144ea`
- Entry source SHA-256 `8719f9a7cfd30e35771c58424afece65b903755be8020905d649b22e0d7dd26b`
- Cold log SHA-256 `d3d74d1dbd7d4992cdf2e13a3a6cb74ab6cddf0de3b7ad439bf43c9aa0591c63`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.
