import OrderedPartitions.MarkedKernelEnvelope

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

def deltaCap (h s : ℕ) : ℝ :=
  |scaledPowerCoeff (h+1) 0| + 2*powerErrorConstant (h+1) +
    ((h:ℝ)+1)*((s:ℝ)+3*(h+1))^h

theorem abs_scaledDelta_le (h s i : ℕ) (hi : i≤s+1) :
    |deltaSeq (scaledPowerCoeff (h+1)) i| ≤ deltaCap h s := by
  have z : 0≤powerErrorConstant (h+1) := by unfold powerErrorConstant; positivity
  cases i with
  | zero =>
    change |scaledPowerCoeff (h+1) 0| ≤ _
    unfold deltaCap
    linarith only [z, show (0:ℝ)≤((h:ℝ)+1)*((s:ℝ)+3*(h+1))^h by positivity]
  | succ i =>
    have is : (i:ℝ)≤s := by exact_mod_cast (show i≤s by omega)
    obtain ⟨ml,mu⟩ := mainIncrement_band h i
    have mp : 0≤mainIncrement (h+1) i := (by positivity : (0:ℝ)≤((h:ℝ)+1)*(i:ℝ)^h).trans ml
    have ub : mainIncrement (h+1) i ≤ ((h:ℝ)+1)*((s:ℝ)+3*(h+1))^h :=
      mu.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) h) (by positivity))
    have e := (geometric_increment_error (h+1) i).trans (div_le_self (by positivity) (one_le_pow₀ (by norm_num) (n:=i)))
    let d := scaledPowerCoeff (h+1) (i+1) - scaledPowerCoeff (h+1) i
    have a := abs_add_le (d-mainIncrement (h+1) i) (mainIncrement (h+1) i)
    rw [sub_add_cancel,abs_of_nonneg mp] at a
    change |d| ≤ _
    change |d-mainIncrement (h+1) i| ≤ _ at e
    unfold deltaCap
    linarith only [a,e,ub,abs_nonneg (scaledPowerCoeff (h+1) 0)]

theorem original_marked_value_band {j : ℕ} (hj : 64≤j) (h s : ℕ) :
    |(h.factorial:ℝ)*normalizedMoment (s+h*j) j h * coeff (s+h*j) K - mainScaled h s| ≤
      (cMass j^h-1)*(((s:ℝ)+2*h)^h+powerErrorConstant h) + ((s:ℝ)+2*h)^h/(2*8^s) := by
  rw [original_moment_scaled (by omega)]
  exact marker_value_error hj h s _ (by unfold powerErrorConstant; positivity) (abs_scaledPower_le h s)

theorem original_marked_increment_band {j : ℕ} (hj : 64≤j) (h s : ℕ) :
    let d := h+1
    let value := fun t : ℕ ↦ (d.factorial:ℝ)*normalizedMoment (t+d*j) j d * coeff (t+d*j) K
    |(value (s+1)-value s)-mainIncrement d s| ≤
      (cMass j^d-1)*deltaCap h s + (((s:ℝ)+1+2*d)^d/8+((s:ℝ)+2*d)^d)/(2*8^s) := by
  dsimp only
  rw [original_moment_scaled (by omega),original_moment_scaled (by omega)]
  exact marker_increment_error hj (h+1) s _ (by unfold deltaCap powerErrorConstant; positivity)
    (abs_scaledDelta_le h s)

#print axioms original_marked_value_band
#print axioms original_marked_increment_band
end OrderedPartitions.Kernel
