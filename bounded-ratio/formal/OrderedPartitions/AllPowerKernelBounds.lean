import OrderedPartitions.AllPowerIncrements

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

def scaledPowerCoeff (h s : ℕ) : ℝ := (h.factorial:ℝ)*coeff s (K^(h+1))

theorem scaledPowerCoeff_error (h s : ℕ) :
    |scaledPowerCoeff h s - mainScaled h s| ≤ ((s:ℝ)+2*h)^h / (2*8^s) := by
  unfold scaledPowerCoeff
  rw [mainScaled_eq, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (h.factorial:ℝ)*(powerMain h s/(2*8^s)) :=
      mul_le_mul_of_nonneg_left (all_power_relative_error h s) (Nat.cast_nonneg _)
    _ = mainScaled h s / (2*8^s) := by rw [mainScaled_eq]; ring
    _ ≤ _ := by gcongr; exact (mainScaled_band h s).2

theorem scaledPowerCoeff_increment_error (h s : ℕ) :
    |(scaledPowerCoeff h (s+1) - scaledPowerCoeff h s) - mainIncrement h s| ≤
      (((s:ℝ)+1+2*h)^h/8 + ((s:ℝ)+2*h)^h)/(2*8^s) := by
  unfold mainIncrement
  rw [show scaledPowerCoeff h (s+1) - scaledPowerCoeff h s - (mainScaled h (s+1) - mainScaled h s) =
      (scaledPowerCoeff h (s+1) - mainScaled h (s+1)) -
        (scaledPowerCoeff h s - mainScaled h s) by ring]
  apply (abs_sub _ _).trans
  have a := add_le_add (scaledPowerCoeff_error h (s+1)) (scaledPowerCoeff_error h s)
  push_cast at a
  apply a.trans_eq
  rw [pow_succ]
  ring

#print axioms scaledPowerCoeff_error
#print axioms scaledPowerCoeff_increment_error
end OrderedPartitions.Kernel
