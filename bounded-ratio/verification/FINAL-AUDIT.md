# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local NVMe project on Linux ARM64. Lean 4.33.1 built all 76 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 76 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separate copy of the existing dependency cache.

The lexical source scan passed. The 199 source reports and 12 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps the bounded-ratio theorem and its two consequences to the original rows.

- Source ZIP SHA-256 `bb69afb9cbcdf967659a4fcd28106f776f2e96efb6f643d2c07d6631cd6efe86`
- Entry source SHA-256 `530dafe6c5464f832861ee01af1b37c5ba9999b4a4b6b94146567116c266364a`
- Cold log SHA-256 `b88160dcab2380919a05ad91309a0ee739d097b9f85e651ae2076b5415efcf94`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.
