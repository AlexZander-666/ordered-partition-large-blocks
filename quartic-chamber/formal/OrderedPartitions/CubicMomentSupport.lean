import OrderedPartitions.QuadraticActual

noncomputable section
namespace OrderedPartitions.Kernel

/-- The positive-degree coefficients in the common affine coordinate enter exactly at
their support threshold. This statement also handles the first rank in each chamber. -/
theorem normalizedMoment_pos_iff {j n : ℕ} (hj : 2≤j) (h : ℕ) :
    0<normalizedMoment n j (h+1) ↔ (h+1)*j≤n := by
  have h1 : 1≤j := by omega
  constructor
  · contrapose!
    intro neg
    exact (normalized_before h1 neg).le
  · intro pn
    have factor := pow_pos (markScale_pos j) (h+1)
    unfold normalizedMoment
    apply div_pos _ factor
    induction n,pn using Nat.le_induction with
    | base => exact div_pos (markedCount_starts h1 h) (original_eval_pos h1 _)
    | succ n le ih => exact ih.trans (original_binomial_moment_strict hj h le)

#print axioms normalizedMoment_pos_iff
end OrderedPartitions.Kernel
