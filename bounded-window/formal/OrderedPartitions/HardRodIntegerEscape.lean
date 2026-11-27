import OrderedPartitions.HardRodEscapeLimit
import OrderedPartitions.HardRodEntryGrowth
import OrderedPartitions.HardRodWindowPoly

/-! The left escaping root of the actual normalized rows at an integral ratio. -/

open Polynomial Filter OrderedPartitions.Kernel
open scoped Topology

namespace OrderedPartitions.HardRod

private theorem window_degree (d j n : ℕ) : (windowPoly d j n).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [windowPoly_coeff, not_le_of_gt hk]

/-- At a size-to-cutoff ratio tending to the integer d from the degree-d layer,
both true normalized rows have the required sign at a lower root eventually
to the left of every fixed threshold. -/
theorem windowPoly_integer_escape {J N : ℕ → ℕ} {d : ℕ} (hd : 2 ≤ d)
    (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 (d:ℝ)))
    (above : ∀ᶠ i in atTop, d*J i ≤ N i) (threshold : ℝ) :
    ∀ᶠ i in atTop, ∃ r : ℝ, r < threshold ∧ (windowPoly d (J i) (N i)).IsRoot r ∧
      0 < (-1)^d*(windowPoly d (J i) (N i+1)).eval r := by
  let L := fun i ↦ N i-d*J i
  let V := fun i ↦ 4*((L i:ℝ)+3)
  let A := fun k ↦ rodCoeff k (d:ℝ)
  let B := fun k : ℕ ↦ if k=0 then 0 else rodCoeff (k-1) ((d:ℝ)-1)
  have x1 : (1:ℝ) < d := by exact_mod_cast (by omega : 1<d)
  have next : 0 < A (d-1) := by
    have eqn : (d:ℝ)-((d-1:ℕ):ℝ)=1 := by rw [Nat.cast_sub (by omega : 1≤d)]; ring
    simp only [A, rodCoeff, eqn, max_eq_left (by norm_num : (0:ℝ) ≤ 1), one_pow]
    positivity
  have leading :
      Tendsto (fun i ↦ (windowPoly d (J i) (N i)).coeff d) atTop (𝓝 0) := by
    simpa only [windowPoly_coeff, le_rfl, if_true, rodCoeff_dead (by omega : 0<d) le_rfl]
      using window_coeff_limit x1 hj hn d
  apply eventually_escape_of_growth (scale := fun i ↦ (J i:ℝ)) (lag := V)
    (oldLimits := A) (diffLimits := B) (by omega) next leading _ _ _ _ _ _ threshold
  · intro k hk
    simpa only [windowPoly_coeff, if_pos hk.le, A] using window_coeff_limit x1 hj hn k
  · intro k hk
    cases k with
    | zero =>
      refine (tendsto_const_nhds (x := (0:ℝ))).congr' ?_
      filter_upwards [hj.eventually_ge_atTop 1] with i ji
      simp [windowPoly_coeff, windowCoeff, normalizedMoment, markedCount_zero,
        (original_eval_pos ji _).ne']
    | succ k =>
      simpa only [windowPoly_coeff, if_pos hk.le, windowSpeed, B,
        Nat.succ_ne_zero, if_false, Nat.succ_sub_one] using window_speed_limit x1 hj hn k
  · exact .of_forall fun i ↦ ⟨window_degree d (J i) (N i), window_degree d (J i) (N i+1)⟩
  · filter_upwards [hj.eventually_ge_atTop 2, above] with i ji ab
    rw [windowPoly_coeff, if_pos le_rfl, ← Nat.sub_add_cancel ab]
    have jp : (0:ℝ) < J i := by exact_mod_cast (by omega : 0 < J i)
    exact ⟨windowCoeff_positive ji (by omega) (L i), jp, by dsimp [V]; positivity⟩
  · filter_upwards [hj.eventually_ge_atTop 2, above] with i ji ab
    have e : L i+d*J i=N i := Nat.sub_add_cancel ab
    simpa only [V, e, windowPoly_coeff, if_pos le_rfl] using
      windowCoeff_relative_growth ji (by omega : 1 ≤ d) (L i)
  · apply entry_lag_ratio_limit hj
    simpa [L] using residual_ratio_limit hj hn d

#print axioms windowPoly_integer_escape

theorem upper_rank_lt_next_layer {J N : ℕ → ℕ} {d : ℕ}
    (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 (d:ℝ))) :
    ∀ᶠ i in atTop, N i+1 < (d+1)*J i := by
  have behind : (d:ℝ) < (d:ℝ)+1/2 := by norm_num
  filter_upwards [hj.eventually_ge_atTop 3, hn.eventually (gt_mem_nhds behind)] with i ji ni
  have jp : 0 < (J i:ℝ) := by exact_mod_cast (by omega : 0 < J i)
  have jthree : (3:ℝ) ≤ J i := by exact_mod_cast ji
  have budget := (div_lt_iff₀ jp).mp ni
  have real : (N i:ℝ)+1 < ((d:ℝ)+1)*(J i:ℝ) := by nlinarith only [budget, jthree]
  exact_mod_cast real

private theorem window_stable {M d j n : ℕ} (hj : 1 ≤ j) (cap : d ≤ M)
    (rank : n < (d+1)*j) : windowPoly M j n = windowPoly d j n := by
  ext k
  by_cases h : k ≤ d
  · simp [windowPoly_coeff, h, h.trans cap]
  · have hl := rank.trans_le (Nat.mul_le_mul_right j (by omega : d+1≤k))
    simp [windowPoly_coeff, h, window_before hj hl]

/-- The escape assertion in the fixed common truncation used by the bounded
real root branches. Both ranks have entered the same degree layer. -/
theorem windowPoly_integer_escape_at_cap {J N : ℕ → ℕ} {d M : ℕ} (hd : 2 ≤ d) (cap : d ≤ M)
    (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 (d:ℝ)))
    (above : ∀ᶠ i in atTop, d*J i ≤ N i) (threshold : ℝ) :
    ∀ᶠ i in atTop, ∃ r : ℝ, r < threshold ∧ (windowPoly M (J i) (N i)).IsRoot r ∧
      0 < (-1)^d*(windowPoly M (J i) (N i+1)).eval r := by
  filter_upwards [windowPoly_integer_escape hd hj hn above threshold,
    upper_rank_lt_next_layer hj hn, hj.eventually_ge_atTop 1] with i found upper ji
  rw [window_stable ji cap (by omega : N i < (d+1)*J i), window_stable ji cap upper]
  exact found

/-- The same sign in the original marking variable. The threshold is
expressed in the common affine coordinate of the two actual rows. -/
theorem original_integer_escape {J N : ℕ → ℕ} {d : ℕ} (hd : 2 ≤ d)
    (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 (d:ℝ)))
    (above : ∀ᶠ i in atTop, d*J i ≤ N i) (threshold : ℝ) :
    ∀ᶠ i in atTop, ∃ t : ℝ, t < 0 ∧ (J i:ℝ)*markScale (J i)*(t-1) < threshold ∧
      (row (N i) (J i)).IsRoot t ∧ 0 < (-1)^d*(row (N i+1) (J i)).eval t := by
  filter_upwards [windowPoly_integer_escape hd hj hn above threshold,
    upper_rank_lt_next_layer hj hn, hj.eventually_ge_atTop 2] with i found upper ji
  obtain ⟨r, rlt, old_root, new_sign⟩ := found
  let s := (J i:ℝ)*markScale (J i)
  let t := 1+r/s
  have jp : (0:ℝ) < J i := by exact_mod_cast (by omega : 0 < J i)
  have sp : 0 < s := mul_pos jp (markScale_pos _)
  have equality : s*(t-1)=r := by dsimp only [t]; field_simp [sp.ne']; ring
  have earlier : N i < (d+1)*J i := by omega
  have op : (row (N i) (J i)).IsRoot t := by
    rw [IsRoot.def, original_windowPoly (by omega : 1≤J i) earlier t]
    change _ * (windowPoly d (J i) (N i)).eval (s*(t-1)) = 0
    rw [equality, show (windowPoly d (J i) (N i)).eval r=0 from old_root, mul_zero]
  have tneg : t<0 := by
    by_contra! h
    exact (QuadraticOrder.original_positive ji (N i) h).ne' op
  refine ⟨t,tneg,equality ▸ rlt,op,?_⟩
  rw [original_windowPoly (by omega : 1≤J i) upper t]
  change 0 < (-1)^d*((row (N i+1) (J i)).eval 1 *
    (windowPoly d (J i) (N i+1)).eval (s*(t-1)))
  rw [equality, mul_left_comm]
  exact mul_pos (original_eval_pos (by omega : 1≤J i) _) new_sign

#print axioms windowPoly_integer_escape_at_cap
#print axioms original_integer_escape

end OrderedPartitions.HardRod
