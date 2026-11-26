# Verification of the original statements

On 27 November 2026 an ARM64 DGX Spark compiled and separately replayed all 43 local Lean modules from a new extraction. The 123 source axiom reports and 48 additional finite-cutoff reports used only propext, Classical.choice and Quot.sound. All nine external Git revisions were checked against the Lake manifest. External library objects were cached. Every project object was rebuilt from source.

The starting objects are surjections from n labels onto a finite ordered set of block positions. The marker counts positions having at least j preimages. Theorem 2 is OrderedPartitions.original_initial_chambers in formal/OrderedPartitions/InitialChambers.lean. Its first-jump factorization is accompanied by row_linear, count_one_positive, first_jump_count and coeff_row. These identify the genuine degrees and the positive quadratic leading coefficient. The quadratic and cubic cases specify complete products and root multisets. Theorem 1 is OrderedPartitions.Kernel.original_binomial_moment_from_entry in formal/OrderedPartitions/AllMoments.lean. Its numerator is identified pointwise with the binomial statistic on the genuine partitions by markedCount_eq_count.

The transcript is cold-kernel.log. Each compiled project source and its replayed object appear in module-receipts.tsv; axioms.tsv identifies the declarations checked. The frozen 43-module ZIP has SHA-256 b281794c89b11ba6023eab529cc6c0eacc28bdb83ec5d95ac866e7bd28cacbf6. The source release verifier and instructions are in formal/. The Python checks and finite integer witness digest are in scripts/ and verification/quadratic-certificate.txt.

The initial-chambers result includes the pair ending at rank 3j. The original all-ranks question remains open. The factorial-moment result applies at arbitrary rank subject to its entry inequality.

The bibliography of the five-page paper refers to the published edition of Ahlbach–Usatine–Pippenger. Both the loose TeX and the TeX ZIP produced the same PDF after two passes in separate workspaces.
