# Verified through the first quartic

27 November 2026. The proof was rebuilt from the exact ZIP with no local project object files. All 81 project modules passed warning-as-error compilation and independent kernel replay. The cold verifier checked 187 source-declared axiom reports and 62 additional finite-cutoff declarations. Every reported dependency was among propext, Classical.choice and Quot.sound.

The public theorem is OrderedPartitions.original_cubic_chamber for 3j≤n<4j, j≥2, and OrderedPartitions.original_through_first_quartic for j≤n<4j. Both refer directly to rows enumerating ordered surjections by the number of fibers of size at least j. The original-row cold evidence includes finite cutoffs 2 through 63, and the integral grid and analytic proof for every cutoff from 64 onward.

Source ZIP SHA-256: `48c5ca6cd26f575fabf869332001560b64febc92b6b02ef03ce0687a6694dee4`. Cold log SHA-256: `21462eeb7891862f7e906d87f3cc0cc23d0aab8dd08a4fbbd89476583f96048c`. Exact per-module sources and replayed objects are in module-receipts.tsv. The externally supplied dependency commits and the Lean executable version are in cold.log.
