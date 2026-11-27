import OrderedPartitions.HardRodNormalizer

noncomputable section
open Filter PowerSeries
open scoped Topology
namespace OrderedPartitions.Kernel

/-- Binomial marking coefficient in the common bounded-ratio variable. -/
def windowCoeff (j n h : ℕ) : ℝ := normalizedMoment n j h / (j:ℝ)^h

private theorem window_raw {j : ℕ} (hj : 1≤j) (s d : ℕ) :
    windowCoeff j (s+d*j) d =
      (scaledMarkedCoeff j d s/(j:ℝ)^d)*(coeff (s+d*j) K)⁻¹/(d.factorial:ℝ) := by
  rw [windowCoeff,← original_moment_scaled hj d s]
  have nz : (j:ℝ)≠0 := by exact_mod_cast (show j≠0 by omega)
  field_simp [(k_pos (s+d*j)).ne']

theorem original_window_limits {J S : ℕ → ℕ} {x : ℝ} (hj : Tendsto J atTop atTop)
    (hs : Tendsto (fun i ↦ (S i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (h : ℕ)
    (edge : h ≠ 0 ∨ Tendsto S atTop atTop) :
    let d := h+1
    let n := fun i ↦ S i + d*J i
    Tendsto (fun i ↦ windowCoeff (J i) (n i) d) atTop (𝓝 (x^d/(d.factorial:ℝ))) ∧
    Tendsto (fun i ↦ (J i:ℝ)*(windowCoeff (J i) (n i+1) d-windowCoeff (J i) (n i) d))
      atTop (𝓝 (((h:ℝ)+1)*x^h/(d.factorial:ℝ))) := by
  dsimp only
  let d := h+1
  let n := fun i ↦ S i + d*J i
  have h0 : ∀ᶠ i in atTop, J i ≤ n i := .of_forall (fun i ↦ by dsimp [n,d]; rw [Nat.succ_mul]; omega)
  have h1 : ∀ᶠ i in atTop, J i ≤ n i+1 := h0.mono (fun i hi ↦ by omega)
  have iv0 := (normalizer_limit hj h0).inv₀ (by norm_num)
  have iv1 := (normalizer_limit hj h1).inv₀ (by norm_num)
  have rate := (weighted_inverse_limit hj h1).sub (weighted_inverse_limit hj h0)
  have value := marked_value_limit hj hs h
  have diff := marked_increment_limit hj hs h edge
  constructor
  · have t := (value.mul iv0).div_const (d.factorial:ℝ)
    apply (show Tendsto _ _ (𝓝 (x^d/(d.factorial:ℝ))) from by simpa [d] using t).congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i ji
    exact (window_raw ji (S i) d).symm
  · have t := ((diff.mul iv1).add (value.mul rate)).div_const (d.factorial:ℝ)
    apply (show Tendsto _ _ (𝓝 (((h:ℝ)+1)*x^h/(d.factorial:ℝ))) from by simpa using t).congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i ji
    have nz : (J i:ℝ) ≠ 0 := by exact_mod_cast (show J i ≠ 0 by omega)
    have sh : n i+1=S i+1+d*J i := by dsimp [n];omega
    change ((_ / (J i:ℝ)^h * (coeff (n i+1) K)⁻¹) + _ / (J i:ℝ)^d *
       ((J i:ℝ)*((coeff (n i+1) K)⁻¹-1) - (J i:ℝ)*((coeff (n i) K)⁻¹-1))) / (d.factorial:ℝ) =
       (J i:ℝ)*(windowCoeff (J i) (n i+1) d-windowCoeff (J i) (n i) d)
    rw [sh,window_raw ji (S i+1) d,window_raw ji (S i) d]
    dsimp only [n,d]
    rw [pow_succ]
    field_simp [nz]
    ring

#print axioms original_window_limits
end OrderedPartitions.Kernel
