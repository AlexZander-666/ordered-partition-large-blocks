import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-! A reciprocal-variable criterion for the leftmost root at a degree boundary. -/

noncomputable section
open Polynomial

namespace OrderedPartitions.HardRod

private theorem eval_head (p : ℝ[X]) (x : ℝ) :
    p.eval x = p.coeff 0 + x*p.divX.eval x := by
  simpa only [eval_add, eval_mul, eval_X, eval_C, add_comm] using
    (congrArg (Polynomial.eval x) (X_mul_divX_add p)).symm

private theorem eval_reciprocal {p : ℝ[X]} {d : ℕ} (deg : p.natDegree ≤ d)
    {x : ℝ} (hx : x ≠ 0) :
    p.eval x⁻¹ = (p.reflect d).eval x * (x⁻¹)^d := by
  let _ : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
  simpa only [eval₂_id, invOf_eq_inv, inv_inv] using
    (eval₂_reflect_mul_pow (RingHom.id ℝ) (x⁻¹) d p deg).symm

/-- The sign of the new row at a far-left zero of the old row follows from
a small old leading coefficient and a large relative increase. The two
remainder bounds are on the unit interval of the reciprocal variable. -/
theorem escape_of_reciprocal_bounds {p q : ℝ[X]} {d : ℕ} (hd : 1 ≤ d)
    (pd : p.natDegree ≤ d) (qd : q.natDegree ≤ d) {M N : ℝ}
    (ha : 0 < p.coeff d) (hb : 0 < p.coeff (d-1))
    (small : 2*p.coeff d/p.coeff (d-1) ≤ 1)
    (old_budget : 4*p.coeff d*M < (p.coeff (d-1))^2)
    (new_budget : 2*p.coeff d*N < p.coeff (d-1)*(q.coeff d-p.coeff d))
    (old_tail : ∀ x : ℝ, |x| ≤ 1 → |((p.reflect d).divX.divX).eval x| ≤ M)
    (new_tail : ∀ x : ℝ, |x| ≤ 1 → |(((q-p).reflect d).divX).eval x| ≤ N) :
    ∃ r : ℝ, r < -(p.coeff (d-1)/(2*p.coeff d)) ∧ p.IsRoot r ∧
      0 < (-1)^d*q.eval r := by
  let A := p.coeff d
  let B := p.coeff (d-1)
  let t := 2*A/B
  have tp : 0 < t := by dsimp [t]; positivity
  have t1 : t ≤ 1 := small
  have tB : t*B = 2*A := div_mul_cancel₀ _ hb.ne'
  let R := p.reflect d
  let S := (q-p).reflect d
  have rhead : R.coeff 0 = A := by simp [R, A]
  have rnext : R.divX.coeff 0 = B := by simp [R, B, coeff_divX, revAt_le hd]
  have shead : S.coeff 0 = q.coeff d-A := by simp [S, A]
  have old_eval (x : ℝ) : R.eval x = A+B*x+x^2*R.divX.divX.eval x := by
    have h := eval_head R x
    have h' := eval_head R.divX x
    rw [rhead, h', rnext] at h
    rw [h]
    ring
  have tM : t^2*M < A := by
    change (2*A/B)^2*M < A
    rw [div_pow, div_mul_eq_mul_div, div_lt_iff₀ (sq_pos_of_pos hb)]
    nlinarith only [mul_lt_mul_of_pos_left old_budget ha]
  have start : R.eval (-t) < 0 := by
    rw [old_eval]
    have ht : |-t| ≤ 1 := by rw [abs_neg, abs_of_pos tp]; exact t1
    have cap := mul_le_mul_of_nonneg_left ((abs_le.mp (old_tail (-t) ht)).2)
      (sq_nonneg t)
    nlinarith only [tM, tB, cap]
  have finish : 0 < R.eval 0 := by rwa [← coeff_zero_eq_eval_zero, rhead]
  obtain ⟨x, hx, hroot⟩ := intermediate_value_Ioo (neg_nonpos.mpr tp.le)
    R.continuous.continuousOn (show (0:ℝ) ∈ Set.Ioo (R.eval (-t)) (R.eval 0)
      from ⟨start, finish⟩)
  change (p.reflect d).eval x = 0 at hroot
  have absx : |x| ≤ t := by rw [abs_of_neg hx.2]; linarith [hx.1]
  have cap := new_tail x (absx.trans t1)
  have change_cap : t*N < q.coeff d-A := by
    change (2*A/B)*N < _
    rw [div_mul_eq_mul_div, div_lt_iff₀ hb]
    simpa only [mul_comm (q.coeff d-A)] using new_budget
  have change_err : |x*S.divX.eval x| ≤ t*N := by
    rw [abs_mul]
    exact mul_le_mul absx cap (abs_nonneg _) tp.le
  have changed : 0 < S.eval x := by
    rw [eval_head S x, shead]
    linarith only [change_cap, (abs_le.mp change_err).1]
  have new_pos : 0 < (q.reflect d).eval x := by
    change 0 < ((q-p).reflect d).eval x at changed
    rw [reflect_sub, eval_sub, hroot, sub_zero] at changed
    exact changed
  have oldzero : p.IsRoot x⁻¹ := by
    rw [IsRoot.def, eval_reciprocal pd hx.2.ne, hroot, zero_mul]
  have left : x⁻¹ < - (B/(2*A)) := by
    have bound := (inv_lt_inv_of_neg hx.2 (neg_lt_zero.mpr tp)).mpr hx.1
    simpa only [t, inv_neg, inv_div] using bound
  refine ⟨x⁻¹, left, oldzero, ?_⟩
  rw [eval_reciprocal qd hx.2.ne]
  have xpos : 0 < -x⁻¹ := neg_pos.mpr (inv_lt_zero'.mpr hx.2)
  have id : (-1 : ℝ)^d * ((q.reflect d).eval x * (x⁻¹)^d) =
      (q.reflect d).eval x * (-x⁻¹)^d := by rw [← neg_one_mul (x⁻¹), mul_pow]; ring
  rw [id]
  exact mul_pos new_pos (pow_pos xpos _)

#print axioms escape_of_reciprocal_bounds

private theorem eval_bound {p : ℝ[X]} {d : ℕ} (degree : p.natDegree ≤ d)
    {x M : ℝ} (x_bound : |x| ≤ 1) (bound : ∀ i, |p.coeff i| ≤ M) :
    |p.eval x| ≤ ((d:ℝ)+1)*M := by
  rw [eval_eq_sum_range' (Nat.lt_succ_iff.mpr degree)]
  refine (Finset.abs_sum_le_sum_abs ..).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (d+1), M := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow]
      exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀
        (abs_nonneg _) x_bound)).trans (bound i)
    _ = _ := by simp [nsmul_eq_mul]

private theorem divX_reflect_bound {p : ℝ[X]} {d : ℕ} (deg : p.natDegree ≤ d)
    {x M : ℝ} (x_bound : |x| ≤ 1) (Mn : 0 ≤ M)
    (bound : ∀ i < d, |p.coeff i| ≤ M) :
    |(p.reflect d).divX.eval x| ≤ ((d:ℝ)+1)*M := by
  have degR : (p.reflect d).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl deg)
  apply eval_bound (natDegree_divX_le.trans degR) x_bound
  intro i
  rw [coeff_divX, coeff_reflect]
  by_cases inside : i+1 ≤ d
  · rw [revAt_le inside]
    exact bound _ (by omega)
  · rw [revAt_eq_self_of_lt (by omega : d < i+1),
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i+1), abs_zero]
    exact Mn

private theorem divX_twice_reflect_bound {p : ℝ[X]} {d : ℕ} (deg : p.natDegree ≤ d)
    {x M : ℝ} (x_bound : |x| ≤ 1) (Mn : 0 ≤ M)
    (bound : ∀ i < d, |p.coeff i| ≤ M) :
    |(p.reflect d).divX.divX.eval x| ≤ ((d:ℝ)+1)*M := by
  have degR : (p.reflect d).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl deg)
  apply eval_bound (natDegree_divX_le.trans (natDegree_divX_le.trans degR)) x_bound
  intro i
  rw [coeff_divX, coeff_divX, coeff_reflect]
  by_cases inside : i+1+1 ≤ d
  · rw [revAt_le inside]
    exact bound _ (by omega)
  · rw [revAt_eq_self_of_lt (by omega : d < i+1+1),
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i+1+1), abs_zero]
    exact Mn

/-- Coefficient bounds give concrete reciprocal remainder bounds. All conditions
are finite inequalities and require no old-root hypothesis. -/
theorem escape_of_coefficient_bounds {p q : ℝ[X]} {d : ℕ} (hd : 1 ≤ d)
    (pd : p.natDegree ≤ d) (qd : q.natDegree ≤ d) {M N : ℝ}
    (Mn : 0 ≤ M) (Nn : 0 ≤ N) (ha : 0 < p.coeff d) (hb : 0 < p.coeff (d-1))
    (small : 2*p.coeff d/p.coeff (d-1) ≤ 1)
    (old_budget : 4*p.coeff d*(((d:ℝ)+1)*M) < (p.coeff (d-1))^2)
    (new_budget : 2*p.coeff d*(((d:ℝ)+1)*N) < p.coeff (d-1)*(q.coeff d-p.coeff d))
    (old_coeff : ∀ i < d, |p.coeff i| ≤ M)
    (new_coeff : ∀ i < d, |q.coeff i-p.coeff i| ≤ N) :
    ∃ r : ℝ, r < -(p.coeff (d-1)/(2*p.coeff d)) ∧ p.IsRoot r ∧
      0 < (-1)^d*q.eval r := by
  apply escape_of_reciprocal_bounds hd pd qd ha hb small old_budget new_budget
  · exact fun x hx ↦ divX_twice_reflect_bound pd hx Mn old_coeff
  · refine fun x hx ↦ divX_reflect_bound
      ((natDegree_sub_le q p).trans (max_le qd pd)) hx Nn ?_
    simpa only [coeff_sub] using new_coeff

#print axioms escape_of_coefficient_bounds

end OrderedPartitions.HardRod
