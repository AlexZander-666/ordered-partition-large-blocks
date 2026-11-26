import OrderedPartitions.CubicChamberBoxNumeric
import OrderedPartitions.CubicChamberSeparation

/-! Transfer the certified rational margins to enclosed real coefficients. -/

namespace OrderedPartitions.CubicChamber.Box

private theorem div_le_of_bounds {a A b B : ℝ} (hA : 0 ≤ A) (num : a ≤ A)
    (denPos : 0 < b) (den : b ≤ B) : a/B ≤ A/b := by
  exact (div_le_div_of_nonneg_right num (denPos.le.trans den)).trans
    (div_le_div_of_nonneg_left hA denPos den)

/-- The rational arithmetic provides the real inputs of the separation theorem. -/
theorem conditions_from_box {cell : Cell} (valid : cell.Valid) {a b c d e f : ℝ}
    (h : Encloses cell a b c d e f) :
    let V : ℝ := cell.bounds.finalUpper
    0 ≤ a ∧ 0 < b ∧ 0 ≤ c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
      d*f/e^2 ≤ 4/25 ∧
      (∀ v : ℝ, 1 ≤ v → v ≤ 5/4 → 1-v+(d*f/e^2)*v^2=0 → v ≤ V) ∧
      V*d*max 0 (b*d-f) < (a*d-e)*e ∧
      V*a*f/(b*e)+c*e/(b*f) < 1 := by
  let B := cell.bounds
  have tests := all_pass cell valid
  unfold Cell.Passes at tests
  obtain ⟨aLow, bLow, dLow, eLow, dHigh, _, fHigh, _, _, capSlack, budgets,
    gapSlack, nearSlack, farSlack⟩ := tests
  have aL : 0 < (B.aLower : ℝ) := by exact_mod_cast aLow
  have bL : 0 < (B.bLower : ℝ) := by exact_mod_cast bLow
  have dL : 0 < (B.dLower : ℝ) := by exact_mod_cast dLow
  have eL : 0 < (B.eLower : ℝ) := by exact_mod_cast eLow
  have dU : 0 < (B.dUpper : ℝ) := by exact_mod_cast dHigh
  have fU : 0 < (B.fUpper : ℝ) := by exact_mod_cast fHigh
  have ha : 0 < a := aL.trans_le h.aLower
  have hb : 0 < b := bL.trans_le h.bLower
  have hd : 0 < d := dL.trans_le h.dLower
  have he : 0 < e := eL.trans_le h.eLower
  have hf := h.fPositive
  have aU := ha.trans_le h.aUpper
  have bU := hb.trans_le h.bUpper
  have castCap : (B.capacity : ℝ) =
      (B.dUpper : ℝ)*(B.fUpper : ℝ)/(B.eLower : ℝ)^2 := by
    simp only [Bounds.capacity, Rat.cast_div, Rat.cast_mul, Rat.cast_pow]
  have H : d*f/e^2 ≤ (B.capacity : ℝ) := by
    rw [castCap]
    exact div_le_of_bounds (mul_nonneg dU.le fU.le)
      (mul_le_mul h.dUpper h.fUpper hf.le dU.le)
      (sq_pos_of_pos eL) (pow_le_pow_left₀ eL.le h.eLower 2)
  have Hslack : (21/1000 : ℝ) < 4/25-(B.capacity : ℝ) := by
    have mapped := (Rat.cast_lt (K := ℝ)).mpr capSlack
    push_cast at mapped
    exact mapped
  have capacity : d*f/e^2 ≤ 4/25 := H.trans (by linarith only [Hslack])
  have budget (k : ℕ) (hk : k < 5) :
      (B.capacity : ℝ)*(upperAt B.capacity k : ℝ) < 1 := by
    exact_mod_cast budgets ⟨k, hk⟩
  have step (k : ℕ) :
      (upperAt B.capacity (k+1) : ℝ) =
        1/(1-(B.capacity : ℝ)*(upperAt B.capacity k : ℝ)) := by
    simp only [upperAt, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_mul]
  have upper_pos : 0 < (B.finalUpper : ℝ) := by
    change 0 < (upperAt B.capacity (4+1) : ℝ)
    rw [step]
    exact one_div_pos.mpr (sub_pos.mpr (budget 4 (by decide)))
  have cap (v : ℝ) (lo : 1 ≤ v) (hi : v ≤ 5/4) (eqn : 1-v+(d*f/e^2)*v^2=0) :
      v ≤ (B.finalUpper : ℝ) := by
    have induct (k : ℕ) (hk : k ≤ 5) : v ≤ (upperAt B.capacity k : ℝ) := by
      induction k with
      | zero => simpa [upperAt] using hi
      | succ k ih =>
        rw [step]
        exact tighten (by linarith) (by positivity) H (ih (by omega)) (budget k (by omega)) eqn
    exact induct 5 (by decide)
  have gapLower : (B.gap : ℝ) ≤ a*d-e := by
    simp only [Bounds.gap, Rat.cast_mul, Rat.cast_sub]
    exact sub_le_sub (mul_le_mul h.aLower h.dLower dL.le ha.le) h.eUpper
  have gapMargin : (964/1000 : ℝ) < (B.gap : ℝ) := by
    have mapped := (Rat.cast_lt (K := ℝ)).mpr gapSlack
    push_cast at mapped
    exact mapped
  have gapPositive : 0 < (B.gap : ℝ) := by linarith only [gapMargin]
  have nearMargin : (35/1000 : ℝ) < (B.nearMargin : ℝ) := by
    have mapped := (Rat.cast_lt (K := ℝ)).mpr nearSlack
    push_cast at mapped
    exact mapped
  simp only [Bounds.nearMargin, Rat.cast_sub, Rat.cast_mul, Rat.cast_max, Rat.cast_zero] at nearMargin
  have hmax : max 0 (b*d-f) ≤ max 0 ((B.bUpper : ℝ)*(B.dUpper : ℝ)-(B.fLower : ℝ)) :=
    max_le_max le_rfl (sub_le_sub (mul_le_mul h.bUpper h.dUpper hd.le bU.le) h.fLower)
  have near : (B.finalUpper : ℝ)*d*max 0 (b*d-f) < (a*d-e)*e := by
    calc
      _ ≤ (B.finalUpper : ℝ)*(B.dUpper : ℝ)*max 0 ((B.bUpper : ℝ)*(B.dUpper : ℝ)-(B.fLower : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h.dUpper upper_pos.le) hmax
          (le_max_left _ _) (mul_nonneg upper_pos.le dU.le)
      _ < (B.gap : ℝ)*(B.eLower : ℝ) := by linarith only [nearMargin]
      _ ≤ _ := mul_le_mul gapLower h.eLower eL.le (gapPositive.le.trans gapLower)
  have ratioNonneg : 0 ≤ (B.ratioUpper : ℝ) := (div_nonneg h.cNonneg hf.le).trans h.ratio
  have farFirst : (B.finalUpper : ℝ)*a*f/(b*e) ≤
      (B.finalUpper : ℝ)*(B.aUpper : ℝ)*(B.fUpper : ℝ)/((B.bLower : ℝ)*(B.eLower : ℝ)) := by
    exact div_le_of_bounds (mul_nonneg (mul_nonneg upper_pos.le aU.le) fU.le)
      (mul_le_mul (mul_le_mul_of_nonneg_left h.aUpper upper_pos.le) h.fUpper
        hf.le (mul_nonneg upper_pos.le aU.le))
      (mul_pos bL eL) (mul_le_mul h.bLower h.eLower eL.le hb.le)
  have farSecond : c*e/(b*f) ≤ (B.ratioUpper : ℝ)*(B.eUpper : ℝ)/(B.bLower : ℝ) := by
    rw [show c*e/(b*f) = (c/f)*e/b by field_simp]
    exact div_le_of_bounds (mul_nonneg ratioNonneg (he.le.trans h.eUpper))
      (mul_le_mul h.ratio h.eUpper he.le ratioNonneg) bL h.bLower
  have farMargin : (136/1000 : ℝ) < (B.farMargin : ℝ) := by
    have mapped := (Rat.cast_lt (K := ℝ)).mpr farSlack
    push_cast at mapped
    exact mapped
  simp only [Bounds.farMargin, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_one] at farMargin
  have far : (B.finalUpper : ℝ)*a*f/(b*e)+c*e/(b*f) < 1 :=
    (add_le_add farFirst farSecond).trans_lt (by linarith only [farMargin])
  exact ⟨ha.le, hb, h.cNonneg, hd, he, hf, capacity, cap, near, far⟩

/-- Every enclosed tuple has the two certified separator roots and opposite cubic signs. -/
theorem separation_from_box {cell : Cell} (valid : cell.Valid) {a b c d e f : ℝ}
    (h : Encloses cell a b c d e f) :
    ∃ w z : ℝ, 0 < w ∧ w < z ∧
      (∀ y : ℝ, d+e*y+f*y^2 = f*(y+w)*(y+z)) ∧
      1-a*w+b*w^2-c*w^3 < 0 ∧ 0 < 1-a*z+b*z^2-c*z^3 := by
  obtain ⟨ha, hb, hc, hd, he, hf, capacity, cap, near, far⟩ := conditions_from_box valid h
  exact separation_points ha hb hc hd he hf capacity cap near far

#print axioms conditions_from_box
#print axioms separation_from_box

end OrderedPartitions.CubicChamber.Box
