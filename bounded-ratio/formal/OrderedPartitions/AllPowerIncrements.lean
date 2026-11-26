import OrderedPartitions.AllPowerGrowth

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

def mainIncrement (h s : ℕ) := mainScaled h (s+1) - mainScaled h s

theorem mainIncrement_step (h s : ℕ) :
    mainIncrement (h+1) s = mainScaled h (s+1) + ((s:ℝ)+2)*mainIncrement h (s+1) +
      (((h:ℝ)+1)*rho)*mainIncrement h s := by
  simp only [mainIncrement,mainScaled,Nat.cast_add,Nat.cast_one]
  ring

/-- Two-sided discrete derivative estimate, with the same leading coefficient on both sides. -/
theorem mainIncrement_band (h s : ℕ) :
    ((h:ℝ)+1)*(s:ℝ)^h ≤ mainIncrement (h+1) s ∧
    mainIncrement (h+1) s ≤ ((h:ℝ)+1)*((s:ℝ)+3*(h+1))^h := by
  have hr := rho_interval
  have r0 : 0 ≤ rho := by linarith
  induction h generalizing s with
  | zero => simp [mainIncrement,mainScaled]
  | succ h ih =>
    let b : ℝ := (s:ℝ)+3*((h:ℝ)+2)
    let u : ℝ := (h:ℝ)+1
    let v : ℝ := ((h:ℝ)+2)*rho
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hv : 0 ≤ v := by dsimp [v]; positivity
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have bound : (s:ℝ)+2+v ≤ b := by
      dsimp [v,b]
      nlinarith only [hr.2, Nat.cast_nonneg (α:=ℝ) h,
        mul_nonneg (show 0≤(h:ℝ) by positivity) (show 0≤1-rho by linarith)]
    obtain ⟨lo,hi⟩ := ih s
    obtain ⟨lo',hi'⟩ := ih (s+1)
    obtain ⟨mlo,mhi⟩ := mainScaled_band (h+1) (s+1)
    rw [mainIncrement_step (h+1)]
    push_cast at lo' hi' mlo mhi ⊢
    have sl : (s:ℝ) ≤ s+1 := by linarith
    have ls : (s:ℝ)^(h+1) ≤ mainScaled (h+1) (s+1) :=
      (pow_le_pow_left₀ (by positivity) sl _).trans mlo
    have us : mainScaled (h+1) (s+1) ≤ b^(h+1) :=
      mhi.trans (pow_le_pow_left₀ (by positivity) (by dsimp [b]; linarith) _)
    have l1 : u*(s:ℝ)^h ≤ mainIncrement (h+1) (s+1) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) sl _) hu).trans lo'
    have u0 : mainIncrement (h+1) s ≤ u*b^h :=
      hi.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by dsimp [b]; linarith) _) hu)
    have u1 : mainIncrement (h+1) (s+1) ≤ u*b^h :=
      hi'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by dsimp [b]; linarith) _) hu)
    change (↑h+1+1)*(s:ℝ)^(h+1) ≤ _ ∧ _ ≤ (↑h+1+1)*((s:ℝ)+3*((↑h+1)+1))^(h+1)
    have hv' : (↑h+1+1)*rho = v := by dsimp [v];ring
    rw [hv']
    have bb : (s:ℝ)+3*((↑h+1)+1) = b := by dsimp [b]; ring
    rw [bb]
    constructor
    · have a := mul_le_mul (by linarith : (s:ℝ)≤s+2) l1 (mul_nonneg hu (by positivity)) (by positivity)
      have z := mul_nonneg hv ((mul_nonneg hu (by positivity)).trans lo)
      dsimp only [u] at a
      rw [pow_succ] at ls ⊢
      linarith only [ls,a,z]
    · have a := mul_le_mul_of_nonneg_left u1 (by positivity : 0≤(s:ℝ)+2)
      have c := mul_le_mul_of_nonneg_left u0 hv
      have d := mul_le_mul_of_nonneg_right bound (mul_nonneg hu (pow_nonneg hb h))
      dsimp only [u] at a c d
      rw [pow_succ] at us ⊢
      linarith only [a,c,d,us]

#print axioms mainIncrement_band
end OrderedPartitions.Kernel
