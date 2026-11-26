import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Directed eighty-place rational bounds on the renewal scale. -/
namespace OrderedPartitions.Renewal
open Finset Real

def rhoLower : ℚ := 69314718055994530941723212145817656807550013436025525412068000949339362196969471 / 10^80
def rhoUpper : ℚ := 69314718055994530941723212145817656807550013436025525412068000949339362196969472 / 10^80

private def logPartial : ℚ := ∑ i ∈ range 280, (1/2 : ℚ)^(i+1)/((i:ℚ)+1)

/-- Enclose log 2 with the real Taylor remainder and a rational partial sum. -/
theorem log_two_interval : (rhoLower : ℝ) ≤ log 2 ∧ log 2 ≤ (rhoUpper : ℝ) := by
  have approx := Real.abs_log_sub_add_sum_range_le (x := (2 : ℝ)⁻¹) (by norm_num) 280
  rw [show (1-(2 : ℝ)⁻¹) = (2 : ℝ)⁻¹ by norm_num, log_inv] at approx
  have castp : (logPartial : ℝ) = ∑ i ∈ range 280, (2 : ℝ)⁻¹^(i+1)/((i:ℝ)+1) := by
    simp [logPartial, Rat.cast_sum, one_div]
  rw [← castp] at approx
  have prec : |(2 : ℝ)⁻¹|^(280+1)/(1-|(2 : ℝ)⁻¹|) = ((1/(2^280) : ℚ) : ℝ) := by norm_num [one_div, inv_pow, pow_succ]
  rw [prec, abs_le] at approx
  have bounds : rhoLower ≤ logPartial - 1/2^280 ∧ logPartial + 1/2^280 ≤ rhoUpper := by
    decide +kernel
  have l : (rhoLower : ℝ) ≤ (logPartial : ℝ) - ((1/2^280 : ℚ):ℝ) := by exact_mod_cast bounds.1
  have u : (logPartial : ℝ) + ((1/2^280 : ℚ):ℝ) ≤ (rhoUpper : ℝ) := by exact_mod_cast bounds.2
  constructor <;> linarith [approx.1, approx.2]

#print axioms log_two_interval
end OrderedPartitions.Renewal
