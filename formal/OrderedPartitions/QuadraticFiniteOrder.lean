import OrderedPartitions.QuadraticFinite
import OrderedPartitions.QuadraticRootOrder

/-! From the signed finite checks to the exact root order of the original rows. -/

open Polynomial

namespace OrderedPartitions.QuadraticExact

open QuadraticOrder

private theorem row_as_cubic {j n : ℕ} (hj : 1 ≤ j) (hn : n < 4*j) :
    row n j = cubic ((row n j).coeff 0) ((row n j).coeff 1) ((row n j).coeff 2)
      ((row n j).coeff 3) := by
  calc
    row n j = (coefficientRow j n).polynomial := original_row hj hn
    _ = _ := by
      rw [original_coefficient hj n 0 (by decide), original_coefficient hj n 1 (by decide),
        original_coefficient hj n 2 (by decide), original_coefficient hj n 3 (by decide)]
      rfl

private theorem row_as_quadratic {j n : ℕ} (hj : 1 ≤ j) (hn : n < 3*j) :
    row n j = quadratic ((row n j).coeff 0) ((row n j).coeff 1) ((row n j).coeff 2) := by
  have h3 : (row n j).coeff 3 = 0 := by
    rw [coeff_row hj, count_above_degree hj hn]
    simp
  calc
    row n j = cubic ((row n j).coeff 0) ((row n j).coeff 1) ((row n j).coeff 2)
        ((row n j).coeff 3) := row_as_cubic hj (by omega)
    _ = _ := by simp [cubic, h3]

/-- The original-row inequalities certify the two precise adjacent root patterns. -/
theorem original_adjacent_of_signs {j n : ℕ} (hj : 1 ≤ j) (hn : n < 3*j)
    (h : OriginalSigns j n) : Adjacent (row n j) (row (n+1) j) (n+1 = 3*j) := by
  unfold OriginalSigns inequalities at h
  rcases h with ⟨ha, hb, hc, hd, _, _, hjump, hu, hv⟩
  have hg : 0 ≤ (row (n+1) j).coeff 3 := by
    rw [coeff_row hj]
    positivity
  have hs := adjacent_of_remainder (e := (row (n+1) j).coeff 1) (f := (row (n+1) j).coeff 2)
    ha hb hc hd hg hu hv
  rw [← row_as_quadratic hj hn, ← row_as_cubic hj (n := n+1) (by omega)] at hs
  simpa only [Adjacent, hjump] using hs

/-- The 1,224 adjacent original pairs have complete simple negative root factorizations. -/
theorem original_adjacent_finite {j n : ℕ} (hj : 2 ≤ j) (hj' : j ≤ 49)
    (lo : 2*j ≤ n) (hi : n < 3*j) :
    Adjacent (row n j) (row (n+1) j) (n+1 = 3*j) :=
  original_adjacent_of_signs (by omega) hi (original_finite hj hj' lo hi)

#print axioms original_adjacent_of_signs
#print axioms original_adjacent_finite

end OrderedPartitions.QuadraticExact
