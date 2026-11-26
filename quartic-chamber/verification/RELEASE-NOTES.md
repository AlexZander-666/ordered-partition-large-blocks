# Review and edition notes

The source-cold Spark build and an independent x86-64 review both rebuilt the same 81 project modules from a clean project directory, reusing precompiled pinned external dependencies. Both replayed every project module in a separate Lean checker process. The module tables from both runs agree byte for byte, including Lean object digests. Each run checked 187 in-source axiom reports and 62 additional finite-cutoff statements. Only propositional extensionality, classical choice and quotient soundness appeared. The independent review obtained a complete result with a serial driver after an earlier parallel attempt did not complete. The serial driver and its patch are included.

The subsequent independent review checked the exact nine-page revised PDF, its corresponding LaTeX archive, and the unchanged Lean source. It confirmed the first support of the cubic at \(m=0\), the common-index estimate for \(c/f_0\), the positive quartic entry, the negative-root readout on the original variable, the connection to Liu–Wang's Theorem 2.1, and the two original-object declarations. It independently reran the four Python checks from the LaTeX archive, with matching outputs. It reused its previous cold Lean result after checking the identical source bytes. Its local TeX Live did not have its PDF format built. The local paper rebuild succeeded with TeX Live 2026.

The final distribution adds the PDF rebuild script and its loose source inputs. A clean extraction reproduces the PDF and LaTeX archive byte for byte. The reviewed PDF, LaTeX archive and all original Lean source files keep their reviewed digests.

- Revised PDF SHA-256 `03a791c0520b55851424550345895d0a793cef0498ad63ff42d873f81c403c7b`
- Reviewed LaTeX archive SHA-256 `f981b17dee584694976b6c7a6772b0f662189a169823637485b4498612d4e0a2`
- Frozen Lean source archive SHA-256 `48c5ca6cd26f575fabf869332001560b64febc92b6b02ef03ce0687a6694dee4`
