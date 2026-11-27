import OrderedPartitions.HardRodScaling

noncomputable section
open Filter PowerSeries
open scoped Topology
namespace OrderedPartitions.Kernel

private theorem absorb_error {X M U D G E : ℕ → ℝ} {u z : ℝ}
    (den : ∀ i, 0 ≤ D i) (bound : ∀ᶠ i in atTop, |X i-M i| ≤ E i*U i + G i)
    (lm : Tendsto (fun i ↦ M i/D i) atTop (𝓝 z))
    (lu : Tendsto (fun i ↦ U i/D i) atTop (𝓝 u)) (le : Tendsto E atTop (𝓝 0))
    (lg : Tendsto (fun i ↦ G i/D i) atTop (𝓝 0)) :
    Tendsto (fun i ↦ X i/D i) atTop (𝓝 z) := by
  have err : Tendsto (fun i ↦ (X i-M i)/D i) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [zero_mul,add_zero] using (le.mul lu).add lg) (.of_forall (fun _ ↦ abs_nonneg _)) ?_
    filter_upwards [bound] with i h
    simp only [Function.comp_apply]
    rw [abs_div,abs_of_nonneg (den i),← mul_div_assoc,← add_div]
    exact div_le_div_of_nonneg_right h (den i)
  have t := lm.add err
  simpa only [add_zero,sub_div,add_sub_cancel] using t

variable {J S : ℕ → ℕ} {x : ℝ}

private theorem constant_error_limit (hj : Tendsto J atTop atTop) (h : ℕ) (c : ℝ) :
    Tendsto (fun i ↦ c/(J i:ℝ)^(h+1)) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using (inv_power_limit hj (h+1)).const_mul c

private theorem marker_cost_limit (hj : Tendsto J atTop atTop) (h : ℕ) :
    Tendsto (fun i ↦ cMass (J i)^h-1) atTop (𝓝 0) := by
  simpa using ((marker_mass_limit hj).pow h).sub_const 1

theorem marked_value_limit (hj : Tendsto J atTop atTop)
    (hs : Tendsto (fun i ↦ (S i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (h : ℕ) :
    Tendsto (fun i ↦ scaledMarkedCoeff (J i) (h+1) (S i)/(J i:ℝ)^(h+1))
      atTop (𝓝 (x^(h+1))) := by
  let d := h+1
  let U := fun i ↦ ((S i:ℝ)+2*d)^d+powerErrorConstant d
  have um : Tendsto (fun i ↦ U i/(J i:ℝ)^d) atTop (𝓝 (x^d)) := by
    simpa only [U,add_div,add_zero] using (shifted_power_limit hj hs (2*d) d).add (constant_error_limit hj h (powerErrorConstant d))
  apply absorb_error (U:=U) (G:=fun _ ↦ powerErrorConstant d) (den:=fun _ ↦ by positivity)
    (lm:=main_scaled_limit hj hs d) (lu:=um) (le:=marker_cost_limit hj d)
    (lg:=constant_error_limit hj h _)
  filter_upwards [hj.eventually_ge_atTop 64] with i ji
  have pos : 0≤powerErrorConstant d := by unfold powerErrorConstant; positivity
  have e := (geometric_power_error d (S i)).trans (div_le_self pos (one_le_pow₀ (by norm_num) (n:=S i)))
  rw [marked_as_convolution]
  apply (abs_sub_le _ (scaledPowerCoeff d (S i)) _).trans
  apply add_le_add _ e
  exact marker_convolution_tail ji d (S i) _ (by dsimp [U]; positivity) (abs_scaledPower_le d (S i))

private theorem residual_limit (hj : Tendsto J atTop atTop) (h : ℕ) (C : ℝ) (hc : 0≤C)
    (edge : h ≠ 0 ∨ Tendsto S atTop atTop) :
    Tendsto (fun i ↦ (C/(2:ℝ)^(S i))/(J i:ℝ)^h) atTop (𝓝 0) := by
  cases h with
  | zero =>
    have inf := edge.resolve_left (by simp)
    simpa using (tendsto_const_nhds (x:=C)).div_atTop ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp inf)
  | succ h =>
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (constant_error_limit hj h C)
    · intro i; positivity
    · intro i; exact div_le_div_of_nonneg_right (div_le_self hc (one_le_pow₀ (by norm_num) (n:=S i))) (by positivity)

theorem marked_increment_limit (hj : Tendsto J atTop atTop)
    (hs : Tendsto (fun i ↦ (S i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (h : ℕ)
    (edge : h ≠ 0 ∨ Tendsto S atTop atTop) :
    Tendsto (fun i ↦ (scaledMarkedCoeff (J i) (h+1) (S i+1)-scaledMarkedCoeff (J i) (h+1) (S i))/(J i:ℝ)^h)
      atTop (𝓝 (((h:ℝ)+1)*x^h)) := by
  let d := h+1
  let c := |scaledPowerCoeff d 0| + 2*powerErrorConstant d
  have cap : Tendsto (fun i ↦ deltaCap h (S i)/(J i:ℝ)^h) atTop (𝓝 (c*(0:ℝ)^h+((h:ℝ)+1)*x^h)) := by
    have t := ((inv_power_limit hj h).const_mul c).add
      ((shifted_power_limit hj hs (3*((h:ℝ)+1)) h).const_mul ((h:ℝ)+1))
    simpa only [deltaCap,c,d,div_eq_mul_inv,add_mul,mul_assoc] using t
  apply absorb_error (U:=fun i ↦ deltaCap h (S i)) (G:=fun i ↦ 2*powerErrorConstant d/(2:ℝ)^(S i))
    (den:=fun _ ↦ by positivity) (lm:=main_increment_limit hj hs h) (lu:=cap) (le:=marker_cost_limit hj d)
    (lg:=residual_limit hj h _ (by unfold powerErrorConstant; positivity) edge)
  filter_upwards [hj.eventually_ge_atTop 64] with i ji
  rw [marked_as_convolution,marked_as_convolution,conv_delta]
  apply (abs_sub_le _ (deltaSeq (scaledPowerCoeff d) (S i+1)) _).trans
  apply add_le_add _ (geometric_increment_error d (S i))
  exact marker_convolution_tail ji d (S i+1) _ (by unfold deltaCap powerErrorConstant; positivity) (abs_scaledDelta_le h (S i))

#print axioms marked_increment_limit
#print axioms marked_value_limit
end OrderedPartitions.Kernel
