import OrderedPartitions.HardRodRawLimits
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open Filter PowerSeries
open scoped Topology
namespace OrderedPartitions.Kernel
variable {J N : ℕ → ℕ}

theorem weighted_normalizer_limit (hj : Tendsto J atTop atTop) (hn : ∀ᶠ i in atTop, J i ≤ N i) :
    Tendsto (fun i ↦ (J i:ℝ)*(coeff (N i) K-1)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have t := (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0:ℝ)≤1/8) (by norm_num)).comp hj
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds t (.of_forall (fun _ ↦ abs_nonneg _)) ?_
  filter_upwards [hn] with i h
  change |(J i:ℝ)*(coeff (N i) K-1)| ≤ (J i:ℝ)*(1/8:ℝ)^(J i)
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (eps_bound (N i)).trans
  rw [div_pow,one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  have m := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤8) h
  linarith only [m,show (0:ℝ)≤8^(N i) by positivity]

theorem normalizer_limit (hj : Tendsto J atTop atTop) (hn : ∀ᶠ i in atTop, J i ≤ N i) :
    Tendsto (fun i ↦ coeff (N i) K) atTop (𝓝 1) := by
  have t := ((weighted_normalizer_limit hj hn).mul (cutoff_inv_limit hj)).add_const 1
  apply (show Tendsto _ _ (𝓝 (1:ℝ)) from by simpa only [mul_zero,zero_add] using t).congr'
  filter_upwards [hj.eventually_ge_atTop 1] with i hi
  have nz : (J i:ℝ)≠0 := by exact_mod_cast (show J i≠0 by omega)
  change (J i:ℝ)*(coeff (N i) K-1)*(J i:ℝ)⁻¹+1=coeff (N i) K
  field_simp
  ring

theorem weighted_inverse_limit (hj : Tendsto J atTop atTop) (hn : ∀ᶠ i in atTop, J i ≤ N i) :
    Tendsto (fun i ↦ (J i:ℝ)*((coeff (N i) K)⁻¹-1)) atTop (𝓝 0) := by
  have t := (weighted_normalizer_limit hj hn).neg.div (normalizer_limit hj hn) (by norm_num)
  apply (show Tendsto _ _ (𝓝 (0:ℝ)) from by simpa using t).congr
  intro i
  change -((J i:ℝ)*(coeff (N i) K-1))/coeff (N i) K=_
  field_simp [(k_pos (N i)).ne']
  ring

#print axioms weighted_inverse_limit
end OrderedPartitions.Kernel
