# Bounded-ratio interlacing for ordered set partitions

For every fixed real C>1, there exists a threshold K(C) such that all consecutive large-block polynomials at ranks n and n+1 have simple negative zeros in strict alternation whenever j≥K(C) and j≤n≤Cj. In particular, any infinite sequence of distinct counterexamples to the full conjecture must have n/j tending to infinity.

An ordered partition is a list of nonempty disjoint blocks covering a labeled set. Each block of size at least j contributes one mark. When both rows have equal degree, each new root lies to the right of its old counterpart. At a degree increase the new roots bracket the old ones. The theorem gives an existence bound for K(C). [Alexandersson’s original problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm) · [Paper](paper/main.pdf)

The proof identifies a family of limiting polynomials by comparing consecutive marked-coefficient arrays. It uses the strict signs of a delay equation, treats the escaping leftmost root separately at integral ratios, and combines the rank chambers by compactness. [Statement map](verification/STATEMENT-MAP.md) · [LaTeX](paper/main.tex)

Lean 4.33.1 checked the original counting definitions, both root orders, multiplicities and the two consequences for exceptional pairs. A clean Spark build and separate kernel replay covered 76 local modules. The 199 source axiom reports and 12 targeted reports use propext, Classical.choice and Quot.sound. [Build report](verification/FINAL-AUDIT.md) · [Reproduction commands](formal/README.md)

Bowen Zuo, East China University of Science and Technology, is the sole responsible author. The manuscript discloses ChatGPT assistance in discovery, proof development, checking and drafting. Version 1.0.0 was prepared in November 2026. Original Lean and reproduction code uses Apache-2.0. The paper is copyright Bowen Zuo. Third-party works retain their licenses. The earlier paper proves a uniform result for ranks through the first cubic row. [Earlier preprint](https://doi.org/10.5281/zenodo.24569711)
