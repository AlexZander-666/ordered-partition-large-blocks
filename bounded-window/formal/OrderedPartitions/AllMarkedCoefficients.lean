import OrderedPartitions.AllPowerKernelBounds
import OrderedPartitions.CubicMarkerMass

noncomputable section
open Finset PowerSeries
namespace OrderedPartitions.Kernel

def scaledMarkedCoeff (j h s : ℕ) := (h.factorial:ℝ)*coeff s (markerB j^h*K^(h+1))

theorem original_moment_scaled {j : ℕ} (hj : 1 ≤ j) (h s : ℕ) :
    (h.factorial:ℝ)*normalizedMoment (s+h*j) j h * coeff (s+h*j) K = scaledMarkedCoeff j h s := by
  rw [normalizedMoment_coeff hj]
  unfold scaledMarkedCoeff
  field_simp [(k_pos (s+h*j)).ne']

theorem marked_as_convolution (j h s : ℕ) :
    scaledMarkedCoeff j h s = convSeq (cWeight j h) (scaledPowerCoeff h) s := by
  rw [scaledMarkedCoeff, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  unfold convSeq cWeight scaledPowerCoeff
  apply sum_congr rfl
  intro i _
  ring

/-- An absolute tail bound, including the signed zero-extended difference kernel. -/
theorem marker_convolution_tail {j : ℕ} (hj : 64≤j) (h s : ℕ) (F : ℕ → ℝ) {U : ℝ}
    (hu : 0≤U) (cap : ∀i≤s, |F i| ≤ U) :
    |convSeq (cWeight j h) F s - F s| ≤ (cMass j^h-1)*U := by
  have mass := cWeight_mass hj h (s+1)
  rw [sum_range_succ',cWeight_zero] at mass
  rw [convSeq,sum_range_succ',cWeight_zero,one_mul,Nat.sub_zero,add_sub_cancel_right]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ range s, cWeight j h (i+1) * U := by
      apply sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (cWeight_nonneg ..)]
      exact mul_le_mul_of_nonneg_left (cap _ (Nat.sub_le ..)) (cWeight_nonneg ..)
    _ = _ := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [mass]) hu

theorem marker_value_error {j : ℕ} (hj : 64≤j) (h s : ℕ) (U : ℝ) (hu : 0≤U)
    (cap : ∀i≤s, |scaledPowerCoeff h i|≤U) :
    |scaledMarkedCoeff j h s - mainScaled h s| ≤
        (cMass j^h-1)*U + ((s:ℝ)+2*h)^h/(2*8^s) := by
  rw [marked_as_convolution]
  apply (abs_sub_le _ (scaledPowerCoeff h s) _).trans
  exact add_le_add (marker_convolution_tail hj h s _ hu cap) (scaledPowerCoeff_error h s)

theorem marker_increment_error {j : ℕ} (hj : 64≤j) (h s : ℕ) (U : ℝ) (hu : 0≤U)
    (cap : ∀i≤s+1, |deltaSeq (scaledPowerCoeff h) i|≤U) :
    |(scaledMarkedCoeff j h (s+1)-scaledMarkedCoeff j h s)-mainIncrement h s| ≤
      (cMass j^h-1)*U + (((s:ℝ)+1+2*h)^h/8+((s:ℝ)+2*h)^h)/(2*8^s) := by
  rw [marked_as_convolution,marked_as_convolution,conv_delta]
  apply (abs_sub_le _ (deltaSeq (scaledPowerCoeff h) (s+1)) _).trans
  exact add_le_add (marker_convolution_tail hj h (s+1) _ hu cap) (scaledPowerCoeff_increment_error h s)

#print axioms original_moment_scaled
#print axioms marker_value_error
#print axioms marker_increment_error
end OrderedPartitions.Kernel
