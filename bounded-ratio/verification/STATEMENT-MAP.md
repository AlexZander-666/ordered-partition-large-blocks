# Statement map

The subject is the original `OrderedPartitions.row n j` from `FirstJumpRows.lean`. An ordered partition is encoded by a surjection from `Fin n` onto an ordered set of block positions. Every fiber of size at least `j` contributes one mark. `row_recurrence` in `LastBlockRow.lean` proves the last-block recurrence from this sample space.

`OrderedPartitions.original_interlacing_bounded_ratio` has the quantifier order

```lean
(C : ℝ) : ∃ K : ℕ, ∀ j ≥ K, ∀ n : ℕ, j ≤ n → (n : ℝ) ≤ C * (j : ℝ) →
  OrderedPartitions.RootTracking.OrderedPair (n / j)
    (OrderedPartitions.row n j) (OrderedPartitions.row (n + 1) j)
```

The ratio cap is placed on the lower rank $n$. The natural quotient $n/j$ fixes the lower degree. `OrderedPair` uses `RootArray` for both rows. If the degree stays the same, the older roots lie to the left in strict alternation. If the degree rises by one, the new row occupies both outer positions. `RootArray.exact` and `RootArray.roots_nodup` give the full factorization and multiplicities, and `RootArray.negative` puts every root below zero.

The delay sign and interlacing of the limiting activity polynomials are audited by `delay_sturm_sign` and `unit_interlacing`. `normalized_stable_pair` handles stable degree, while `normalized_entry_pair` and `original_integer_escape` handle integer ratios. `original_ordered_pair` transfers the root arrays to the original variables. `bounded_ratio_of_integer_entries` combines the chambers under the fixed cap.

`finite_exceptional_rows` and `exceptional_ratio_tendsto` are in `HardRodExceptions.lean`. The first fixes $C$ and takes all exceptional pairs with $2\le j\le n\le Cj$. The second applies to any injective sequence of threshold/rank pairs that fail the same root conclusion and requires $2\le j\le n$ at each index. Its conclusion is $n/j\to+\infty$ in the real ratio.
