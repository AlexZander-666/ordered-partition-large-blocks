import OrderedPartitions.MeanKernel
import OrderedPartitions.FirstJumpRows

/-! Roots of consecutive linear rows on the original ordered partitions. -/

noncomputable section
open Polynomial
namespace OrderedPartitions.Kernel

/-- In the affine chamber, successive rows have unique negative roots which
move strictly to the right when one label is added. -/
theorem original_affine_roots {j n : ℕ} (hj : 2 ≤ j) (hn : j ≤ n) (hnext : n+1 < 2*j) :
    ∃ l r : ℝ, l < r ∧ r < 0 ∧
      (∀ x : ℝ, (row n j).IsRoot x ↔ x = l) ∧
      (∀ x : ℝ, (row (n+1) j).IsRoot x ↔ x = r) := by
  let u (k : ℕ) := (count k j 0 : ℝ)
  let v (k : ℕ) := (count k j 1 : ℝ)
  have hu (k : ℕ) : 0 < u k := by
    dsimp [u]
    exact_mod_cast count_zero_positive k hj
  have hv (k : ℕ) (hk : j ≤ k) : 0 < v k := by
    dsimp [v]
    exact_mod_cast count_one_positive (j := j) (by omega) hk
  have form (k : ℕ) (hk : k < 2*j) : row k j = C (u k) + C (v k)*X :=
    row_linear hj hk
  have order := original_mean_strict hj hn
  rw [form n (by omega), form (n+1) hnext] at order
  simp only [derivative_add, derivative_C, derivative_C_mul_X, zero_add,
    eval_C, eval_add, eval_mul, eval_X, mul_one] at order
  have vn := hv n hn
  have vs := hv (n+1) (by omega)
  have det := (div_lt_div_iff₀ (add_pos (hu n) vn) (add_pos (hu (n+1)) vs)).mp order
  have unique (k : ℕ) (small : k < 2*j) (pos : 0 < v k) (x : ℝ) :
      (row k j).IsRoot x ↔ x = -u k / v k := by
    rw [Polynomial.IsRoot, form k small, eq_div_iff pos.ne']
    simp only [eval_add, eval_mul, eval_C, eval_X]
    constructor <;> intro hx <;> linarith [mul_comm x (v k)]
  refine ⟨-u n / v n, -u (n+1) / v (n+1), ?_, div_neg_of_neg_of_pos (neg_lt_zero.mpr (hu _)) vs,
    unique n (by omega) vn, unique (n+1) hnext vs⟩
  apply (div_lt_div_iff₀ vn vs).mpr
  nlinarith only [det]

#print axioms original_affine_roots
end OrderedPartitions.Kernel
