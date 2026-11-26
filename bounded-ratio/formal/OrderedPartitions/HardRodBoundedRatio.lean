import OrderedPartitions.HardRodRatioTransfer
import OrderedPartitions.HardRodEntryPair

noncomputable section
namespace OrderedPartitions
open Filter Kernel RootTracking HardRod
open scoped Topology

/-- For every fixed real ratio cap, all sufficiently large thresholds give strict
interlacing of the original ordered-partition rows everywhere below that cap.
The root arrays account for the full degrees, including the new root at a jump. -/
theorem original_interlacing_bounded_ratio (C : ℝ) :
    ∃ K : ℕ, ∀ j≥K, ∀ n : ℕ, j≤n → (n:ℝ)≤C*(j:ℝ) →
      OrderedPair (n/j) (row n j) (row (n+1) j) := by
  apply bounded_ratio_of_integer_entries _ C
  intro d J N hj hn rank
  have conv : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 ((d+2:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hn
  have normalized := normalized_entry_pair (D:=d+2) (by omega) hj conv
    (Eventually.of_forall (fun i ↦ (rank i).1))
  filter_upwards [normalized,upper_rank_lt_next_layer hj conv,hj.eventually_ge_atTop 2]
    with i pair cap big
  exact original_ordered_pair big cap pair

#print axioms original_interlacing_bounded_ratio
end OrderedPartitions
