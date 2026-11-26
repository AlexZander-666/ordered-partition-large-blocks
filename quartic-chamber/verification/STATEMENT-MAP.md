# Scope and statement map

For each natural rank \(n\), positions of the \(b\) blocks are the elements of the ordered set \(\operatorname{Fin}(b)\). A surjection from \(\operatorname{Fin}(n)\) onto these positions determines the ordered partition, with unordered fibers. The statistic counts fibers of cardinality **at least** \(j\). The module `FirstJump` defines the finite layers and their cardinalities; `FirstJumpRows.row` sums these counts with a power of the variable for every marked block. In Lean all three definitions (`Layer`, `count`, `row`) are in the namespace `OrderedPartitions`.

The source ZIP has top module `OrderedPartitions.CubicChamberVerified`. Its two unconditional declarations are:

* `OrderedPartitions.original_cubic_chamber` uses \(2\le j\) and \(3j\le n<4j\). For two cubic rows the six distinct roots occur in the order old, new, old, new, old, new. When \(n+1=4j\), a further new root is strictly to the left of this list. All seven or six roots are negative. The predicates `ThreeToThree` and `ThreeToFour` use `ExactRoots`, which gives multiset equality with the displayed roots, and a factorization with the original leading coefficient.
* `OrderedPartitions.original_through_first_quartic` joins this to the earlier adjacent-row statements and covers \(j\le n<4j\) for \(j\ge2\). Its conclusion splits on \(n<3j\); the lower-rank branch is precisely `InitialRootOrder`. The first adjacent pair beyond its hypotheses has lower rank \(4j\).

For the cubic proof the original row is evaluated after a positive affine substitution at both ranks. \(j\ge64\) uses the exact renewal series, the point estimates for the first three marking coefficients, the fourth-order correction and the closed-cell arithmetic. \(2\le j\le63\) uses the original last-block recurrence and exact pseudo-remainders for 2,015 pairs. Both branches feed the same root predicate on the original count polynomials. The verification does not require a nonzero root assumption.

The clean process accepts exactly the locked external package commits, rebuilds all 81 local modules, runs each local module through the independent Lean checker and inspects the named axiom outputs. The 62 standalone finite-cutoff checks supplement those outputs. Its accepted axioms are propositional extensionality, classical choice and quotient soundness.
