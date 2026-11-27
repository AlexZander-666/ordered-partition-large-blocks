import OrderedPartitions.HardRodFullPeriodLeading
import OrderedPartitions.InterlacingStep

/-! A test separating two escaping negative roots by just the two top coefficients. -/
noncomputable section
namespace OrderedPartitions.InterlacingStep
open Finset Polynomial

theorem RootArray.next_coeff_sum {d : ℕ} {p : ℝ[X]} {xs : Fin d → ℝ}
    (hp : RootArray p xs) (hd : 0 < d) :
    p.coeff (d-1) = -p.coeff d * ∑ i, xs i := by
  have split : p.Splits := splits_iff_card_roots.mpr (by simp [hp.exact.roots, hp.degree])
  have eqn := split.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [nextCoeff_of_natDegree_pos (hp.degree ▸ hd), leadingCoeff, hp.degree, hp.exact.roots] at eqn
  simpa [List.sum_ofFn] using eqn

/-- Provided both rows split negatively, a strictly larger mean root modulus
in the new row than the sum of all old moduli separates the two left edges. -/
theorem RootArray.farther_at_full_period {d : ℕ} {p q : ℝ[X]}
    {xs : Fin d → ℝ} {ys : Fin (d+1) → ℝ} (hp : RootArray p xs) (hq : RootArray q ys)
    (hd : 0 < d) (ap : 0 < p.coeff d) (aq : 0 < q.coeff (d+1))
    (gap : ((d:ℝ)+1)*p.coeff (d-1)*q.coeff (d+1) < q.coeff d*p.coeff d)
    (i : Fin d) : ys 0 < xs i := by
  have so := hp.next_coeff_sum hd
  have sn := hq.next_coeff_sum (Nat.succ_pos d)
  rw [Nat.add_sub_cancel] at sn
  have old : ∑ k, xs k ≤ xs i := by
    have h := single_le_sum (f:=fun i ↦ -xs i)
      (fun a _ ↦ neg_nonneg.mpr (hp.negative a).le) (mem_univ i)
    simpa using h
  have new : ((d:ℝ)+1)*ys 0 ≤ ∑ k, ys k := by
    have h := sum_le_sum (s:=univ) (fun k _ ↦ hq.ordered.monotone (Fin.zero_le k))
    simpa [nsmul_eq_mul] using h
  have cmp : ∑ k, ys k < ((d:ℝ)+1)*(∑ k, xs k) := by
    apply (mul_lt_mul_iff_of_pos_right (mul_pos ap aq)).mp
    rw [so,sn] at gap
    linarith only [gap]
  have : ((d:ℝ)+1)*ys 0 < ((d:ℝ)+1)*xs i :=
    new.trans_lt (cmp.trans_le (mul_le_mul_of_nonneg_left old (by positivity)))
  exact (mul_lt_mul_iff_right₀ (by positivity : 0 < (d:ℝ)+1)).mp this

#print axioms RootArray.farther_at_full_period
end OrderedPartitions.InterlacingStep
