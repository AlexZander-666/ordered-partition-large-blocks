import OrderedPartitions.HardRodOriginalLimits

noncomputable section
open Filter PowerSeries
open scoped Topology
namespace OrderedPartitions.Kernel

theorem residual_ratio_limit {J N : ℕ → ℕ} {x : ℝ} (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (d : ℕ) :
    Tendsto (fun i ↦ ((N i-d*J i:ℕ):ℝ)/(J i:ℝ)) atTop (𝓝 (max (x-d) 0)) := by
  apply ((hn.sub_const (d:ℝ)).max (tendsto_const_nhds (x:=(0:ℝ)))).congr'
  filter_upwards [hj.eventually_ge_atTop 1] with i ji
  have jp : 0<(J i:ℝ) := by exact_mod_cast (show 0<J i by omega)
  by_cases hh : d*J i≤N i
  · rw [Nat.cast_sub hh,Nat.cast_mul,sub_div,mul_div_cancel_right₀ _ jp.ne']
    apply max_eq_left
    have cs : (d:ℝ)*(J i:ℝ)≤(N i:ℝ) := by exact_mod_cast hh
    exact sub_nonneg.mpr ((le_div_iff₀ jp).mpr cs)
  · rw [Nat.sub_eq_zero_of_le (by omega : N i≤d*J i),Nat.cast_zero,zero_div]
    apply max_eq_right
    have cs : (N i:ℝ)≤(d:ℝ)*(J i:ℝ) := by exact_mod_cast (show N i≤d*J i by omega)
    exact sub_nonpos.mpr ((div_le_iff₀ jp).mpr cs)

theorem window_before {j n d : ℕ} (hj : 1≤j) (hn : n<d*j) : windowCoeff j n d = 0 := by
  simp [windowCoeff,normalized_before hj hn]

theorem entry_value (j d : ℕ) (hj : 1≤j) :
    windowCoeff j (d*j) d =
      (constantCoeff K)^(d+1)/(coeff (d*j) K)/(j:ℝ)^d := by
  have v := normalizedMoment_coeff hj d 0
  simp only [zero_add,coeff_zero_eq_constantCoeff_apply,map_mul,map_pow] at v
  have b : constantCoeff (markerB j)=1 := by simpa only [coeff_zero_eq_constantCoeff_apply] using marker_zero j
  simp [windowCoeff,v,b]

theorem entry_speed_limit {J : ℕ → ℕ} (hj : Tendsto J atTop atTop) (h : ℕ) :
    Tendsto (fun i ↦ (J i:ℝ)*windowCoeff (J i) ((h+2)*J i) (h+2)) atTop (𝓝 0) := by
  let d := h+2
  have ge : ∀ᶠ i in atTop, J i ≤ d*J i := .of_forall (fun i ↦ by dsimp [d]; rw [Nat.succ_mul];omega)
  have den := (normalizer_limit hj ge).inv₀ (by norm_num)
  have t := ((inv_power_limit hj (h+1)).mul den).const_mul ((constantCoeff K)^(d+1))
  apply (show Tendsto _ _ (𝓝 (0:ℝ)) from by simpa using t).congr'
  filter_upwards [hj.eventually_ge_atTop 1] with i ji
  rw [entry_value _ _ ji]
  change _=(J i:ℝ)*(_/_/(J i:ℝ)^(h+1+1))
  rw [pow_succ (J i:ℝ) (h+1)]
  have nz : (J i:ℝ)≠0 := by exact_mod_cast (show J i≠0 by omega)
  dsimp only [d]
  field_simp [nz]

#print axioms residual_ratio_limit
#print axioms entry_speed_limit
end OrderedPartitions.Kernel
