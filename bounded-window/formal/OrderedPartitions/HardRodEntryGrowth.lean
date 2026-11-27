import OrderedPartitions.HardRodRelativeGrowth
import OrderedPartitions.HardRodOriginalLimits
import OrderedPartitions.AllMoments

/-! The relative increment in the actual hard-rod scaling. -/

open Filter
open scoped Topology

namespace OrderedPartitions.Kernel

theorem windowCoeff_relative_growth {j d : ℕ} (hj : 2 ≤ j) (hd : 1 ≤ d) (m : ℕ) :
    windowCoeff j (m+d*j) d ≤ 4*((m:ℝ)+3) *
      (windowCoeff j (m+d*j+1) d-windowCoeff j (m+d*j) d) := by
  unfold windowCoeff
  rw [← sub_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (normalizedMoment_relative_growth hj hd m) (by positivity)

theorem windowCoeff_positive {j d : ℕ} (hj : 2 ≤ j) (hd : 1 ≤ d) (m : ℕ) :
    0 < windowCoeff j (m+d*j) d := by
  induction m with
  | zero =>
    obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    have count := markedCount_starts (by omega : 1 ≤ j) h
    have value := original_eval_pos (by omega : 1 ≤ j) ((h+1)*j)
    simp only [Nat.zero_add, windowCoeff, normalizedMoment]
    exact div_pos (div_pos (div_pos count value) (pow_pos (markScale_pos j) _))
      (pow_pos (by exact_mod_cast (by omega : 0 < j)) _)
  | succ m ih =>
    have gr := windowCoeff_relative_growth hj hd m
    rw [show m.succ+d*j=m+d*j+1 by omega]
    have step : 0 < windowCoeff j (m+d*j+1) d-windowCoeff j (m+d*j) d :=
      pos_of_mul_pos_right (ih.trans_le gr) (by positivity)
    linarith only [ih, step]

theorem entry_lag_ratio_limit {J M : ℕ → ℕ} (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ 4*((M i:ℝ)+3)/(J i:ℝ)) atTop (𝓝 0) := by
  have e := (hm.add ((cutoff_inv_limit hj).const_mul (3:ℝ))).const_mul (4:ℝ)
  simpa only [div_eq_mul_inv, mul_assoc, add_mul, mul_zero, add_zero] using e

#print axioms windowCoeff_relative_growth
#print axioms windowCoeff_positive
#print axioms entry_lag_ratio_limit

end OrderedPartitions.Kernel
