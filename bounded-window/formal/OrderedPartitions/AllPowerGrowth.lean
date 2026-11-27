import OrderedPartitions.AllPowerApproximation

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

/-- Cancelling the factorial yields a recurrence with positive polynomial coefficients. -/
def mainScaled : ℕ → ℕ → ℝ
  | 0, _ => 1
  | h+1, s => ((s:ℝ)+1)*mainScaled h (s+1) + (((h:ℝ)+1)*rho)*mainScaled h s

theorem mainScaled_eq (h s : ℕ) :
    mainScaled h s = (h.factorial:ℝ)*powerMain h s := by
  induction h generalizing s with
  | zero => simp [mainScaled, powerMain]
  | succ h ih =>
    rw [mainScaled, ih, ih, powerMain, Nat.factorial_succ]
    push_cast
    field_simp

theorem mainScaled_band (h s : ℕ) :
    (s:ℝ)^h ≤ mainScaled h s ∧ mainScaled h s ≤ ((s:ℝ)+2*h)^h := by
  have hr := rho_interval
  have r0 : 0 ≤ rho := by linarith
  induction h generalizing s with
  | zero => simp [mainScaled]
  | succ h ih =>
    obtain ⟨l,u⟩ := ih s
    obtain ⟨l',u'⟩ := ih (s+1)
    push_cast at l' u' ⊢
    change _ ≤ ((s:ℝ)+1)*mainScaled h (s+1) + (((h:ℝ)+1)*rho)*mainScaled h s ∧
        ((s:ℝ)+1)*mainScaled h (s+1) + (((h:ℝ)+1)*rho)*mainScaled h s ≤ _
    let b : ℝ := (s:ℝ)+2*((h:ℝ)+1)
    have p : 0 ≤ mainScaled h s := (by positivity : 0 ≤ (s:ℝ)^h).trans l
    have u1 : mainScaled h (s+1) ≤ b^h := u'.trans (pow_le_pow_left₀ (by positivity) (by dsimp [b]; linarith) h)
    have u0 : mainScaled h s ≤ b^h := u.trans (pow_le_pow_left₀ (by positivity) (by dsimp [b]; linarith) h)
    have l1 : (s:ℝ)^h ≤ mainScaled h (s+1) := (pow_le_pow_left₀ (by positivity) (by linarith : (s:ℝ)≤s+1) h).trans l'
    have c : (s:ℝ)+1 + ((h:ℝ)+1)*rho ≤ b := by
      dsimp [b]
      nlinarith only [hr.2, mul_nonneg (show 0 ≤ (h:ℝ) by positivity) (show 0 ≤ 2-rho by linarith)]
    constructor
    · rw [pow_succ]
      have a := mul_le_mul (show (s:ℝ)≤s+1 by linarith) l1 (by positivity) (by positivity)
      have t := mul_nonneg (mul_nonneg (show 0≤(h:ℝ)+1 by positivity) r0) p
      linarith only [a,t]
    · change _ ≤ b^(h+1)
      rw [pow_succ]
      have a := add_le_add (mul_le_mul_of_nonneg_left u1 (by positivity : 0≤(s:ℝ)+1))
        (mul_le_mul_of_nonneg_left u0 (by positivity : 0≤((h:ℝ)+1)*rho))
      have t := mul_le_mul_of_nonneg_right c (show 0 ≤ b^h by dsimp [b]; positivity)
      linarith only [a,t]

#print axioms mainScaled_eq
#print axioms mainScaled_band
end OrderedPartitions.Kernel
