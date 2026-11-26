import OrderedPartitions.CubicChamberBoxes
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Cast.Order

/-! Closed-cell coverage, including the upper boundaries and the quartic line. -/

namespace OrderedPartitions.CubicChamber.Box

/-- The real point (q,u) lies in the rational cell. -/
def Cell.Contains (cell : Cell) (q u : ℝ) : Prop :=
  (cell.qLo : ℝ) ≤ q ∧ q ≤ (cell.qHi : ℝ) ∧
    (cell.uLo : ℝ) ≤ u ∧ u ≤ (cell.uHi : ℝ)

private theorem cover_unit_steps {k : ℕ} (hk : 0 < k) {x : ℝ} (h0 : 0 ≤ x) (hx : x ≤ k) :
    ∃ i : Fin k, (i.val : ℝ) ≤ x ∧ x ≤ (i.val : ℝ)+1 := by
  let n := ⌊x⌋₊
  have low : (n : ℝ) ≤ x := Nat.floor_le h0
  have high : x < (n : ℝ)+1 := Nat.lt_floor_add_one x
  by_cases hn : n < k
  · exact ⟨⟨n, hn⟩, low, high.le⟩
  · have boundary : ((k-1 : ℕ):ℝ)+1 = (k : ℝ) := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ k)
    have below : (k : ℝ) ≤ x :=
      (show (k : ℝ) ≤ n by exact_mod_cast (le_of_not_gt hn)).trans low
    refine ⟨⟨k-1, by omega⟩, ?_, ?_⟩
    · change ((k-1 : ℕ):ℝ) ≤ x
      linarith
    · simpa only [boundary] using hx

/-- The closed grid covers the complete parameter rectangle, and a point on the
quartic line belongs to a cell admitted for the quartic correction. -/
theorem cover_coordinates {q u : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/64)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (jump : Bool) (entry : jump = true → u+q = 1) :
    ∃ cell : Cell, cell.jump = jump ∧ cell.Valid ∧ cell.Contains q u := by
  obtain ⟨iq, hqlo, hqhi⟩ := cover_unit_steps (k := 6) (by decide)
    (x := 384*q) (by positivity) (by simpa using (show 384*q ≤ (6 : ℝ) by linarith))
  obtain ⟨iu, hulo, huhi⟩ := cover_unit_steps (k := 128) (by decide)
    (x := 128*u) (by positivity) (by simpa using (show 128*u ≤ (128 : ℝ) by linarith))
  let cell : Cell := ⟨iq, iu, jump⟩
  have qlo : (cell.qLo : ℝ) ≤ q := by
    dsimp [cell, Cell.qLo]
    push_cast
    apply (div_le_iff₀ (by norm_num : 0 < (64 : ℝ)*6)).mpr
    linarith
  have qhi : q ≤ (cell.qHi : ℝ) := by
    dsimp [cell, Cell.qHi]
    push_cast
    apply (le_div_iff₀ (by norm_num : 0 < (64 : ℝ)*6)).mpr
    linarith
  have ulo : (cell.uLo : ℝ) ≤ u := by
    dsimp [cell, Cell.uLo]
    push_cast
    apply (div_le_iff₀ (by norm_num : 0 < (128 : ℝ))).mpr
    linarith
  have uhi : u ≤ (cell.uHi : ℝ) := by
    dsimp [cell, Cell.uHi]
    push_cast
    apply (le_div_iff₀ (by norm_num : 0 < (128 : ℝ))).mpr
    linarith
  refine ⟨cell, rfl, ?_, qlo, qhi, ulo, uhi⟩
  intro atEntry
  have equation := entry atEntry
  exact ⟨by exact_mod_cast (show (cell.uLo : ℝ) ≤ 1-(cell.qLo : ℝ) by linarith),
    by exact_mod_cast (show 1-(cell.qHi : ℝ) ≤ (cell.uHi : ℝ) by linarith)⟩

/-- The actual parameter point belongs to an admitted cell for every j ≥ 64. -/
theorem cover_dimensions {j m : ℕ} (hj : 64 ≤ j) (hm : m < j) :
    ∃ cell : Cell, cell.jump = decide (m+1 = j) ∧ cell.Valid ∧
      cell.Contains (1/(j : ℝ)) ((m : ℝ)/(j : ℝ)) := by
  have jpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have qcap : 1/(j : ℝ) ≤ 1/64 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hj)
  have ucap : (m : ℝ)/(j : ℝ) ≤ 1 :=
    (div_le_iff₀ jpos).mpr (by simpa only [one_mul] using (show (m : ℝ) ≤ j by exact_mod_cast hm.le))
  refine cover_coordinates (by positivity) qcap (by positivity) ucap (decide (m+1 = j)) ?_
  intro entry
  have eq : (m : ℝ)+1 = (j : ℝ) := by exact_mod_cast (of_decide_eq_true entry)
  rw [← add_div, eq, div_self jpos.ne']

#print axioms cover_coordinates
#print axioms cover_dimensions

end OrderedPartitions.CubicChamber.Box
