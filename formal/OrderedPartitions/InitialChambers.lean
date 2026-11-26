import OrderedPartitions.AffineRoots
import OrderedPartitions.QuadraticLarge
import OrderedPartitions.QuadraticFiniteOrder
import OrderedPartitions.FirstJumpVerified

/-! Exact adjacent root orders up to and including the first cubic row.
The four possible degree patterns use the actual enumerators on ordered set partitions. -/

noncomputable section
namespace OrderedPartitions
open Kernel QuadraticOrder

/-- Throughout the quadratic platform, the next row alternates strictly with the
current row. Its third root appears exactly at rank three times the threshold. -/
theorem original_quadratic_chamber {j n : ℕ} (hj : 2 ≤ j) (lo : 2*j ≤ n) (hi : n < 3*j) :
    Adjacent (row n j) (row (n+1) j) (n+1 = 3*j) := by
  by_cases large : 50 ≤ j
  · have h := original_quadratic_large (m:=n-2*j) large (by omega)
    simpa only [show 2*j+(n-2*j)=n by omega] using h
  · exact QuadraticExact.original_adjacent_finite hj (by omega) lo hi

/-- The root statement appropriate to each degree pair at ranks from j to 3j−1. -/
def InitialRootOrder (n j : ℕ) : Prop :=
  if n+1 < 2*j then
    ∃ l r : ℝ, l < r ∧ r < 0 ∧
      (∀ x : ℝ, (row n j).IsRoot x ↔ x = l) ∧
      (∀ x : ℝ, (row (n+1) j).IsRoot x ↔ x = r)
  else if n+1 = 2*j then
    ∃ l m r : ℝ, l < m ∧ m < r ∧ r < 0 ∧ (row n j).IsRoot m ∧
      ∀ x : ℝ, (row (n+1) j).eval x = (row (n+1) j).coeff 2 * (x-l) * (x-r)
  else Adjacent (row n j) (row (n+1) j) (n+1=3*j)

/-- All adjacent pairs from the first linear row through the first cubic row
strictly interlace, for every admissible threshold. -/
theorem original_initial_chambers {j n : ℕ} (hj : 2 ≤ j) (lo : j ≤ n) (hi : n < 3*j) :
    InitialRootOrder n j := by
  unfold InitialRootOrder
  split_ifs with linear jump
  · exact original_affine_roots hj lo linear
  · have h := original_first_jump hj
    simpa only [← jump, Nat.add_sub_cancel] using h
  · exact original_quadratic_chamber hj (by omega) hi

#print axioms original_quadratic_chamber
#print axioms original_initial_chambers
#print axioms OrderedPartitions.Kernel.original_binomial_moment_from_entry
end OrderedPartitions
