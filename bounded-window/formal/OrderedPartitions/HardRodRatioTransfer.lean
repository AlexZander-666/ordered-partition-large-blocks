import OrderedPartitions.HardRodFirstChamber
import OrderedPartitions.HardRodCompactness

noncomputable section
namespace OrderedPartitions.RootTracking
open Filter Kernel
open scoped Topology

/-- A bounded ratio reduces to the integer entry cases of chambers of degree at least two. -/
theorem bounded_ratio_of_integer_entries
    (entry : ∀ d : ℕ, ∀ {J N : ℕ→ℕ}, Tendsto J atTop atTop →
      Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 ((d:ℝ)+2)) →
      (∀ i,(d+2)*J i≤N i ∧ N i<(d+3)*J i) →
      ∀ᶠ i in atTop, OrderedPair (d+2) (row (N i) (J i)) (row (N i+1) (J i))) (C : ℝ) :
    ∃ K : ℕ, ∀ j≥K, ∀ n : ℕ, j≤n → (n:ℝ)≤C*(j:ℝ) →
      OrderedPair (n/j) (row n j) (row (n+1) j) := by
  apply uniform_ratio_of_chambers (fun j n ↦ OrderedPair (n/j) (row n j) (row (n+1) j)) _ C
  intro D positive
  apply uniform_chamber_of_limits _ D
  intro J N x xl xu hj hn rank
  have core : ∀ᶠ i in atTop, OrderedPair D (row (N i) (J i)) (row (N i+1) (J i)) := by
    by_cases interior : (D:ℝ)<x
    · obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D≠0)
      have small := normalized_stable_pair (d:=d) (by push_cast at interior; linarith)
        (by push_cast at xu; linarith) hj hn (Eventually.of_forall rank)
      filter_upwards [small,hj.eventually_ge_atTop 2] with i norm big
      have top := (rank i).2
      have room : (d+2)*J i < (d+3)*J i := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      apply original_ordered_pair big _ norm
      exact (Nat.succ_le_of_lt top).trans_lt room
    · have eqn : x=(D:ℝ) := le_antisymm (le_of_not_gt interior) xl
      subst x
      cases D with
      | zero => omega
      | succ a =>
        cases a with
        | zero =>
          exact original_at_ratio_one hj (by simpa using hn) (fun i ↦ by simpa using (rank i).1)
        | succ d => exact entry d hj (by norm_num [Nat.cast_succ,add_assoc] at hn ⊢;exact hn) rank
  filter_upwards [core,hj.eventually_ge_atTop 1] with i valid big
  have degree : N i/J i=D := Nat.div_eq_of_lt_le (rank i).1 (rank i).2
  simpa only [degree] using valid

#print axioms bounded_ratio_of_integer_entries
end OrderedPartitions.RootTracking
