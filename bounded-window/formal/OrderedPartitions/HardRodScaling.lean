import OrderedPartitions.OriginalMarkedBands
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter PowerSeries
open scoped Topology
namespace OrderedPartitions.Kernel

variable {J S : ℕ → ℕ} {x : ℝ}

theorem cutoff_inv_limit (hj : Tendsto J atTop atTop) :
    Tendsto (fun i ↦ (J i : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hj)

theorem marker_mass_limit (hj : Tendsto J atTop atTop) :
    Tendsto (fun i ↦ cMass (J i)) atTop (𝓝 1) := by
  have t := ((tendsto_const_nhds (x := (1:ℝ))).sub ((cutoff_inv_limit hj).const_mul 0.7))
  simpa [cMass,cq,one_div] using t.inv₀ (by norm_num)

theorem shifted_power_limit (hj : Tendsto J atTop atTop)
    (hs : Tendsto (fun i ↦ (S i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (c : ℝ) (h : ℕ) :
    Tendsto (fun i ↦ ((S i:ℝ)+c)^h / (J i:ℝ)^h) atTop (𝓝 (x^h)) := by
  have t := (hs.add ((cutoff_inv_limit hj).const_mul c)).pow h
  simpa only [mul_zero,add_zero,div_eq_mul_inv,← add_mul, mul_pow,inv_pow] using t

theorem inv_power_limit (hj : Tendsto J atTop atTop) (h : ℕ) :
    Tendsto (fun i ↦ ((J i:ℝ)^h)⁻¹) atTop (𝓝 ((0:ℝ)^h)) := by
  simpa [inv_pow] using (cutoff_inv_limit hj).pow h

theorem main_scaled_limit (hj : Tendsto J atTop atTop)
    (hs : Tendsto (fun i ↦ (S i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (h : ℕ) :
    Tendsto (fun i ↦ mainScaled h (S i)/(J i:ℝ)^h) atTop (𝓝 (x^h)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using shifted_power_limit hj hs 0 h)
    (shifted_power_limit hj hs (2*h) h)
  · intro i; exact div_le_div_of_nonneg_right (mainScaled_band h (S i)).1 (by positivity)
  · intro i; exact div_le_div_of_nonneg_right (mainScaled_band h (S i)).2 (by positivity)

theorem main_increment_limit (hj : Tendsto J atTop atTop)
    (hs : Tendsto (fun i ↦ (S i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (h : ℕ) :
    Tendsto (fun i ↦ mainIncrement (h+1) (S i)/(J i:ℝ)^h) atTop (𝓝 (((h:ℝ)+1)*x^h)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (((shifted_power_limit hj hs 0 h).const_mul ((h:ℝ)+1)))
    (((shifted_power_limit hj hs (3*((h:ℝ)+1)) h).const_mul ((h:ℝ)+1)))
  · intro i; simp only [add_zero,← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mainIncrement_band h (S i)).1 (by positivity)
  · intro i; simp only [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mainIncrement_band h (S i)).2 (by positivity)

#print axioms main_scaled_limit
#print axioms main_increment_limit
end OrderedPartitions.Kernel
