import OrderedPartitions.AllMarkedCoefficients
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

def powerErrorConstant (h : ℕ) : ℝ := (h.factorial:ℝ)*Real.exp (2*h)

theorem geometric_power_error (h s : ℕ) :
    |scaledPowerCoeff h s-mainScaled h s| ≤ powerErrorConstant h / (2:ℝ)^s := by
  apply (scaledPowerCoeff_error h s).trans
  have en := (div_le_iff₀ (by positivity : (0:ℝ)<h.factorial)).mp
    (Real.pow_div_factorial_le_exp _ (by positivity : 0≤(s:ℝ)+2*h) h)
  rw [Real.exp_add,show Real.exp (s:ℝ)=(Real.exp 1)^s by simp [← Real.exp_nat_mul]] at en
  have c := pow_le_pow_left₀ (Real.exp_pos 1).le (show Real.exp 1≤4 by linarith [Real.exp_one_lt_three]) s
  have hp : ((s:ℝ)+2*h)^h ≤ (4:ℝ)^s * powerErrorConstant h := by
    unfold powerErrorConstant
    calc
      _ ≤ _ := en
      _ ≤ ((4:ℝ)^s*Real.exp (2*h))*(h.factorial:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c (Real.exp_pos _).le) (Nat.cast_nonneg _)
      _ = _ := by ring
  rw [show (8:ℝ)^s=(2:ℝ)^s*4^s by rw [← mul_pow];norm_num]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have a := mul_le_mul_of_nonneg_right hp (show 0≤(2:ℝ)^s by positivity)
  have z : 0≤(4:ℝ)^s * powerErrorConstant h * 2^s := by unfold powerErrorConstant; positivity
  linarith only [a,z]

theorem geometric_increment_error (h s : ℕ) :
    |(scaledPowerCoeff h (s+1)-scaledPowerCoeff h s)-mainIncrement h s| ≤
        2*powerErrorConstant h/(2:ℝ)^s := by
  unfold mainIncrement
  rw [show scaledPowerCoeff h (s+1) - scaledPowerCoeff h s - (mainScaled h (s+1)-mainScaled h s) =
      (scaledPowerCoeff h (s+1) - mainScaled h (s+1)) - (scaledPowerCoeff h s-mainScaled h s) by ring]
  apply (abs_sub _ _).trans
  have a := add_le_add (geometric_power_error h (s+1)) (geometric_power_error h s)
  apply a.trans
  rw [pow_succ]
  have z : 0≤powerErrorConstant h := by unfold powerErrorConstant; positivity
  have pos : 0<(2:ℝ)^s := by positivity
  field_simp
  linarith

theorem abs_scaledPower_le (h s i : ℕ) (hi : i≤s) :
    |scaledPowerCoeff h i| ≤ ((s:ℝ)+2*h)^h+powerErrorConstant h := by
  have m := mainScaled_band h i
  have p : 0 ≤ mainScaled h i := (by positivity : 0 ≤ (i:ℝ)^h).trans m.1
  have up : mainScaled h i ≤ ((s:ℝ)+2*h)^h :=
    m.2.trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hi (2*h)) _)
  have z : 0≤powerErrorConstant h := by unfold powerErrorConstant; positivity
  have c := (geometric_power_error h i).trans (div_le_self z (one_le_pow₀ (by norm_num) (n:=i)))
  have e := abs_add_le (scaledPowerCoeff h i-mainScaled h i) (mainScaled h i)
  rw [sub_add_cancel,abs_of_nonneg p] at e
  linarith

#print axioms geometric_power_error
#print axioms geometric_increment_error
#print axioms abs_scaledPower_le
end OrderedPartitions.Kernel
