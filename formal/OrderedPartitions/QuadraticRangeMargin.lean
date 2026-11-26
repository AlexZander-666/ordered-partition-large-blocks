import OrderedPartitions.QuadraticBracketing

/-! Scalar margins for the quadratic platform and the first cubic row. -/
namespace OrderedPartitions.QuadraticRange

/-- The one possible cubic contribution can be absorbed into the adjacent increments. -/
theorem corrected_bounds {j m a b c da db : ℝ} (hj : 50 ≤ j) (hm : 0 ≤ m)
    (ha : 0 ≤ a) (ha' : a ≤ 1.02*(j+m+3)) (hb : 0.49*(m+1)*(m+2) ≤ b)
    (hc : 0 ≤ c) (hc' : c ≤ 4) (edge : c = 0 ∨ m = j-1)
    (ha₁ : 0.99 ≤ da) (ha₂ : da ≤ 1.04) (hb₁ : m+1.9 ≤ db) (hb₂ : db ≤ 1.04*(m+4)) :
    0.98 ≤ da - c/b ∧ da-c/b ≤ 1.04 ∧
      m+1.5 ≤ db-c*a/b ∧ db-c*a/b ≤ 1.04*(m+4) := by
  have bpos : 0 < b := lt_of_lt_of_le (by positivity) hb
  have s₀ : 0 ≤ c/b := div_nonneg hc bpos.le
  have t₀ : 0 ≤ c*a/b := div_nonneg (mul_nonneg hc ha) bpos.le
  rcases edge with h|h
  · subst c
    simp only [zero_div, sub_zero, zero_mul]
    exact ⟨by linarith, ha₂, by linarith, hb₂⟩
  · subst m
    have cb : c/b ≤ 0.01 := (div_le_iff₀ bpos).mpr (by
      nlinarith [mul_nonneg (show 0 ≤ j-50 by linarith) (show 0 ≤ j+51 by linarith)])
    have cab : c*a/b ≤ 0.4 := (div_le_iff₀ bpos).mpr (by
      have aux := mul_le_mul_of_nonneg_right hc' ha
      nlinarith [mul_nonneg (show 0 ≤ j-50 by linarith) (show 0 ≤ j+1 by linarith)])
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The negative test value at -S/T, with all divisions cleared. -/
theorem decisive_margin {j m a b S T : ℝ} (hj : 50 ≤ j) (hm : 0 ≤ m) (hmj : m < j)
    (ha : j+m ≤ a) (hb : b ≤ 0.52*(m+4)^2) (hb₀ : 0 ≤ b)
    (hs : 0.98 ≤ S) (hs' : S ≤ 1.04) (ht : m+1.5 ≤ T) (ht' : T ≤ 1.04*(m+4)) :
    T^2-a*S*T+b*S^2 < 0 := by
  have sp : 0 < S := by linarith
  have tp : 0 < T := by linarith
  have mpos : 0 ≤ m+4 := by linarith
  have r₁ : T/S ≤ 1.07*(m+4) := (div_le_iff₀ sp).mpr (by
    nlinarith [mul_nonneg mpos (sub_nonneg.mpr hs)])
  have r₂ : b*S/T ≤ 0.55*(m+11) := (div_le_iff₀ tp).mpr (by
    have bnd := mul_le_mul_of_nonneg_left hs' hb₀
    have tnd := mul_nonneg (show 0 ≤ m+11 by linarith) (sub_nonneg.mpr ht)
    nlinarith [sq_nonneg m])
  have gap : T/S + b*S/T < a := by linarith
  field_simp [sp.ne',tp.ne'] at gap
  nlinarith

/-- The signs at both roots, expressed without a degree-specific choice of brackets. -/
theorem signed_at_roots {a b c da db S T : ℝ} (hb : 0 < b) (hs : 0 < S) (ht : 0 < T)
    (hS : S = da-c/b) (hT : T = db-c*a/b)
    (hmargin : T^2-a*S*T+b*S^2 < 0) :
    let P := fun y : ℝ ↦ 1+a*y+b*y^2
    let Q := fun y : ℝ ↦ 1+(a+da)*y+(b+db)*y^2+c*y^3
    ∃ l r : ℝ, l < -S/T ∧ -S/T < r ∧ r < 0 ∧
      (∀ y, P y = b*(y-l)*(y-r)) ∧ 0 < Q l ∧ Q r < 0 := by
  obtain ⟨l,r,hl,hr,hr0,hfac⟩ := (first_jump_brackets_iff S T 1 a b hs ht (by norm_num) hb).mp
    (by simpa only [one_mul] using hmargin)
  have rem (y : ℝ) (hy : 1+a*y+b*y^2=0) :
      1+(a+da)*y+(b+db)*y^2+c*y^3 = y*(S+T*y) := by
    rw [hS,hT]
    field_simp [hb.ne']
    linear_combination (b+c*y) * hy
  have ql := rem l (by simpa using hfac l)
  have qr := rem r (by simpa using hfac r)
  refine ⟨l,r,hl,hr,hr0,hfac,?_,?_⟩
  · change 0 < 1+(a+da)*l+(b+db)*l^2+c*l^3
    rw [ql]
    exact mul_pos_of_neg_of_neg (lt_trans (lt_trans hl hr) hr0)
      (by linarith [(lt_div_iff₀ ht).mp hl])
  · change 1+(a+da)*r+(b+db)*r^2+c*r^3 < 0
    rw [qr]
    exact mul_neg_of_neg_of_pos hr0 (by linarith [(div_lt_iff₀ ht).mp hr])

#print axioms corrected_bounds
#print axioms decisive_margin
#print axioms signed_at_roots
end OrderedPartitions.QuadraticRange
