import OrderedPartitions.HardRodFullPeriodLeading
import OrderedPartitions.HardRodFullPeriodVieta
import OrderedPartitions.HardRodWindowPoly

noncomputable section
namespace OrderedPartitions.Kernel
open Filter InterlacingStep
open scoped Topology

/-- The coefficient just below the disappearing top degree has a positive
limit, even at the first boundary where the limiting old row is constant. -/
theorem full_period_subleading_limit {J M : ℕ → ℕ} (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) (r : ℕ) :
    Tendsto (fun i ↦ windowCoeff (J i) (M i+(r+1)*J i) r) atTop
      (𝓝 (1/(r.factorial:ℝ))) := by
  cases r with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, div_one]
    apply (tendsto_const_nhds (x:=(1:ℝ))).congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i ji
    simp [windowCoeff,normalizedMoment,markedCount_zero,(original_eval_pos ji _).ne']
  | succ u =>
    have more : Tendsto (fun i ↦ M i+J i) atTop atTop :=
      tendsto_atTop_mono (fun i ↦ Nat.le_add_left (J i) (M i)) hj
    have ratio : Tendsto (fun i ↦ ((M i+J i:ℕ):ℝ)/(J i:ℝ)) atTop (𝓝 1) := by
      apply (show Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)+1) atTop (𝓝 1) from by
        simpa using hm.add_const 1).congr'
      filter_upwards [hj.eventually_ge_atTop 1] with i ji
      rw [Nat.cast_add,add_div,div_self (by exact_mod_cast (by omega : J i ≠ 0))]
    have result := (original_window_limits hj ratio u (Or.inr more)).1
    simpa only [Nat.succ_eq_add_one,Nat.add_mul,one_mul,one_pow,Nat.add_assoc,Nat.add_left_comm,
      Nat.add_comm] using result

/-- Relative loss of the true top coefficient at a full-period jump. -/
theorem full_period_leading_ratio_limit {J M : ℕ → ℕ} (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun i ↦ windowCoeff (J i) (M i+(d+1)*J i) (d+1) /
      windowCoeff (J i) (M i+d*J i) d) atTop (𝓝 0) := by
  have hi : Tendsto (fun i ↦ 18*((M i:ℝ)+1)/(J i:ℝ)) atTop (𝓝 0) := by
    have b := (hm.add (cutoff_inv_limit hj)).const_mul (18:ℝ)
    simpa only [mul_zero,add_zero,div_eq_mul_inv,add_mul,one_mul,mul_assoc] using b
  apply squeeze_zero' _ _ hi
  · filter_upwards [hj.eventually_ge_atTop 2] with i ji
    exact div_nonneg (windowCoeff_positive ji (by omega) _).le (windowCoeff_positive ji hd _).le
  · filter_upwards [hj.eventually_ge_atTop 50] with i ji
    have a := windowCoeff_positive (by omega : 2 ≤ J i) hd (M i)
    have jp : 0 < (J i:ℝ) := by exact_mod_cast (by omega : 0<J i)
    apply (div_le_div_iff₀ a jp).mpr
    simpa only [mul_comm (windowCoeff _ _ _)] using full_period_leading_bound ji d (M i)

/-- At any integral limiting ratio entered from the upper side the
full-period successor has a root strictly farther left than every old root.
The arrays describe the actual normalized rows; this formulation applies
to any complete arrays supplied by the bounded-ratio adjacent theorem. -/
theorem full_period_left_edge {J M : ℕ → ℕ} (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) (r : ℕ) :
    ∀ᶠ i in atTop, ∀ (xs : Fin (r+1) → ℝ) (ys : Fin (r+2) → ℝ),
      RootArray (windowPoly (r+1) (J i) (M i+(r+1)*J i)) xs →
      RootArray (windowPoly (r+2) (J i) (M i+(r+2)*J i)) ys →
      ∀ k, ys 0 < xs k := by
  let A := fun i ↦ windowCoeff (J i) (M i+(r+1)*J i) (r+1)
  let A' := fun i ↦ windowCoeff (J i) (M i+(r+2)*J i) (r+2)
  let B := fun i ↦ windowCoeff (J i) (M i+(r+1)*J i) r
  let B' := fun i ↦ windowCoeff (J i) (M i+(r+2)*J i) (r+1)
  have cost : Tendsto (fun i ↦ ((r:ℝ)+2)*B i*(A' i/A i)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((full_period_subleading_limit hj hm r).const_mul
      ((r:ℝ)+2)).mul (full_period_leading_ratio_limit hj hm (Nat.succ_pos r))
  have gain : Tendsto B' atTop (𝓝 (1/((r+1).factorial:ℝ))) :=
    full_period_subleading_limit hj hm (r+1)
  filter_upwards [cost.eventually_lt gain (by positivity),hj.eventually_ge_atTop 2] with i gap ji
  intro xs ys hp hq k
  have ap : 0 < A i := windowCoeff_positive ji (by omega) _
  have aq : 0 < A' i := windowCoeff_positive ji (by omega) _
  have budget : ((r:ℝ)+2)*B i*A' i < B' i*A i := by
    exact (div_lt_iff₀ ap).mp (by simpa only [mul_div_assoc] using gap)
  apply hp.farther_at_full_period hq (Nat.succ_pos r)
  · simpa [windowPoly_coeff] using ap
  · simpa [windowPoly_coeff] using aq
  · simpa [windowPoly_coeff,B,B',A,A',Nat.cast_add,add_assoc, one_add_one_eq_two] using budget

#print axioms full_period_left_edge
#print axioms full_period_subleading_limit
#print axioms full_period_leading_ratio_limit
end OrderedPartitions.Kernel
