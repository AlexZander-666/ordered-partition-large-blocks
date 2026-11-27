import OrderedPartitions.CubicPairSeparation

/-! Two-scale root separation from the normalized difference of consecutive cubics.
The estimates keep the large and the small root of the quadratic difference separate. -/
noncomputable section
namespace OrderedPartitions.CubicChamber

/-- The quadratic equation has a near solution of size at most 5/4 after the
scaling w=(d/e)v. The same v describes its far solution by Vieta's formula. -/
theorem near_parameter {h : ℝ} (hp : 0 < h) (hu : h ≤ 4/25) :
    ∃ v : ℝ, 1 ≤ v ∧ v ≤ 5/4 ∧ 1-v+h*v^2=0 := by
  let F := fun v : ℝ ↦ 1-v+h*v^2
  have cont : Continuous F := by dsimp [F]; fun_prop
  have left : 0 ≤ F 1 := by dsimp [F]; nlinarith
  have right : F (5/4) ≤ 0 := by dsimp [F]; nlinarith
  have mid := intermediate_value_Icc' (show (1:ℝ) ≤ 5/4 by norm_num)
    cont.continuousOn (show 0 ∈ Set.Icc (F (5/4)) (F 1) from ⟨right,left⟩)
  obtain ⟨v,⟨lo,hi⟩,hv⟩ := mid
  exact ⟨v,lo,hi,hv⟩

/-- An enclosure H of h improves an upper bound V on the near parameter. Iteration
uses rational arithmetic and only requires a positive reciprocal denominator. -/
theorem tighten {h H v V : ℝ} (hv : 0 < v) (hh : 0 ≤ h) (hH : h ≤ H)
    (vV : v ≤ V) (budget : H*V < 1) (eqn : 1-v+h*v^2=0) :
    v ≤ 1/(1-H*V) := by
  apply (le_div_iff₀ (sub_pos.mpr budget)).mpr
  have mono := mul_le_mul hH vV hv.le (hh.trans hH)
  nlinarith only [mul_le_mul_of_nonneg_left mono hv.le, eqn]

/-- At the two positive w values for which d−ew+fw² vanishes,
the old cubic evaluated at −w has opposite signs. -/
theorem near_far_signs {a b c d e f V w z : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hw : 0 < w) (hz : 0 < z) (Hw : d-e*w+f*w^2=0)
    (small : w*e ≤ V*d) (large : e ≤ V*f*z) (outer : z*f ≤ e)
    (near : V*d*max 0 (b*d-f) < (a*d-e)*e)
    (far : V*a*f/(b*e)+c*e/(b*f)<1) (hb : 0 < b) :
    1-a*w+b*w^2-c*w^3 < 0 ∧ 0 < 1-a*z+b*z^2-c*z^3 := by
  have cut : w*(b*d-f) < a*d-e := by
    apply (mul_lt_mul_iff_of_pos_right he).mp
    have h₁ := mul_le_mul_of_nonneg_left (le_max_right (0:ℝ) (b*d-f)) (mul_nonneg hw.le he.le)
    have h₂ := mul_le_mul_of_nonneg_right small (le_max_left (0:ℝ) (b*d-f))
    nlinarith only [h₁,h₂,near]
  have left := mul_lt_mul_of_pos_left cut hw
  have extra : 0 ≤ d*c*w^3 := by positivity
  constructor
  · apply lt_of_mul_lt_mul_left (a:=d) _ hd.le
    nlinarith only [left, Hw, extra]
  · field_simp [hb,he,hf] at far
    have ac := mul_le_mul_of_nonneg_left large ha
    have cz := mul_le_mul_of_nonneg_left outer hc
    have core : a + c*z^2 < b*z := by
      apply (mul_lt_mul_iff_of_pos_right (mul_pos he hf)).mp
      nlinarith only [mul_lt_mul_of_pos_right far hz,
        mul_le_mul_of_nonneg_right ac hf.le,
        mul_le_mul_of_nonneg_right cz (mul_nonneg he.le hz.le)]
    have positive := mul_lt_mul_of_pos_right core hz
    nlinarith only [positive]

/-- The two zeros of the quadratic difference, with the bounds used by the
old-cubic sign estimate. The parameter V may be tightened with any number of steps. -/
theorem separation_points {a b c d e f V : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 ≤ c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (capacity : d*f/e^2 ≤ 4/25)
    (cap : ∀ v : ℝ, 1 ≤ v → v ≤ 5/4 → 1-v+(d*f/e^2)*v^2=0 → v ≤ V)
    (near : V*d*max 0 (b*d-f) < (a*d-e)*e)
    (far : V*a*f/(b*e)+c*e/(b*f)<1) :
    ∃ w z : ℝ, 0 < w ∧ w < z ∧
      (∀ y : ℝ, d+e*y+f*y^2 = f*(y+w)*(y+z)) ∧
      1-a*w+b*w^2-c*w^3 < 0 ∧ 0 < 1-a*z+b*z^2-c*z^3 := by
  obtain ⟨v,lo,hi,eqn⟩ := near_parameter (div_pos (mul_pos hd hf) (sq_pos_of_pos he)) capacity
  have vV := cap v lo hi eqn
  have vp : 0<v := by linarith
  let w := d*v/e
  let z := e/(f*v)
  have wp : 0 < w := div_pos (mul_pos hd vp) he
  have zp : 0 < z := div_pos he (mul_pos hf vp)
  have root := eqn
  field_simp [he.ne'] at root
  have wz : w < z := by
    apply (div_lt_div_iff₀ he (mul_pos hf vp)).mpr
    nlinarith only [root, mul_nonneg (sq_nonneg e) (sub_nonneg.mpr hi), sq_pos_of_pos he]
  have sum : f*(w+z)=e := by
    dsimp [w,z]
    field_simp [he.ne',hf.ne',vp.ne']
    nlinarith only [root]
  have prod : f*w*z=d := by
    dsimp [w,z]
    field_simp
  have fac (y : ℝ) : d+e*y+f*y^2=f*(y+w)*(y+z) := by
    linear_combination -y*sum-prod
  have value := fac (-w)
  have H : d-e*w+f*w^2=0 := by nlinarith only [value]
  have nearCap : w*e ≤ V*d := by
    dsimp [w]
    rw [div_mul_cancel₀ _ he.ne']
    nlinarith only [mul_le_mul_of_nonneg_left vV hd.le]
  have farCap : e ≤ V*f*z := by
    dsimp [z]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (mul_pos hf vp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right vV (mul_nonneg he.le hf.le)]
  have outside : z*f ≤ e := by
    dsimp [z]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hf vp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right lo (mul_nonneg he.le hf.le)]
  exact ⟨w,z,wp,wz,fac,near_far_signs ha hc hd he hf wp zp H nearCap farCap outside near far hb⟩

#print axioms separation_points
#print axioms near_parameter
#print axioms tighten
#print axioms near_far_signs
end OrderedPartitions.CubicChamber
