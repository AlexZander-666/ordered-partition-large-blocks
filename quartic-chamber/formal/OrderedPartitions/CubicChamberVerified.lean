import OrderedPartitions.CubicEntireLarge
import OrderedPartitions.CubicFinite
import OrderedPartitions.InitialChambers

/-! The entire cubic chamber and the combined range through the first quartic. -/
noncomputable section
namespace OrderedPartitions

/-- Exact simple negative root factorizations of both original polynomials, in increasing
alternating order. The new fourth root lies to the left of the old three. -/
theorem original_cubic_chamber {j n : ℕ} (hj : 2≤j) (lo : 3*j≤n) (hi : n<4*j) :
    QuadraticOrder.CubicAdjacent (row n j) (row (n+1) j) (n+1=4*j) := by
  by_cases large : 64≤j
  · exact CubicChamber.original_large large lo hi
  · exact CubicFinite.original_finite hj (by omega) lo hi

/-- The adjacent-row statements spanning the initial linear, quadratic and cubic
lower rows, with the original rows themselves on both sides. -/
theorem original_through_first_quartic {j n : ℕ} (hj : 2≤j) (lo : j≤n) (hi : n<4*j) :
    if n<3*j then InitialRootOrder n j
    else QuadraticOrder.CubicAdjacent (row n j) (row (n+1) j) (n+1=4*j) := by
  split_ifs with hn
  · exact original_initial_chambers hj lo hn
  · exact original_cubic_chamber hj (by omega) hi

#print axioms original_cubic_chamber
#print axioms original_through_first_quartic
end OrderedPartitions
