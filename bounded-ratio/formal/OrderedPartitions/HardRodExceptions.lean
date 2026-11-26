import OrderedPartitions.HardRodBoundedRatio
import Mathlib.Order.Filter.Cofinite

noncomputable section
namespace OrderedPartitions
open RootTracking Filter Set

/-- Ordered pairs store the threshold first and the lower rank second. -/
def exceptionalRows (C : ℝ) : Set (ℕ × ℕ) :=
  {z | 2≤z.1 ∧ z.1≤z.2 ∧ (z.2:ℝ)≤C*(z.1:ℝ) ∧
    ¬ OrderedPair (z.2/z.1) (row z.2 z.1) (row (z.2+1) z.1)}

theorem finite_exceptional_rows (C : ℝ) : (exceptionalRows C).Finite := by
  obtain ⟨K,good⟩ := original_interlacing_bounded_ratio C
  obtain ⟨L,bound⟩ := exists_nat_ge C
  refine ((Finset.range K ×ˢ Finset.range (L*K+1)).finite_toSet).subset ?_
  rintro ⟨j,n⟩ ⟨_,lo,hi,fail⟩
  have small : j<K := by
    by_contra! ge
    exact fail (good j ge n lo hi)
  have nsmall : n≤L*j := by
    exact_mod_cast hi.trans (mul_le_mul_of_nonneg_right bound (Nat.cast_nonneg j))
  have upper : n≤L*K := nsmall.trans (Nat.mul_le_mul_left L small.le)
  simpa using And.intro small (Nat.lt_succ_of_le upper)

/-- Any sequence of pairwise distinct counterexamples must escape every bounded ratio. -/
theorem exceptional_ratio_tendsto {J N : ℕ→ℕ}
    (distinct : Function.Injective (fun i ↦ (J i,N i)))
    (bad : ∀ i,2≤J i ∧ J i≤N i ∧
      ¬ OrderedPair (N i/J i) (row (N i) (J i)) (row (N i+1) (J i))) :
    Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro c
  have avoid := distinct.tendsto_cofinite.eventually (finite_exceptional_rows c).eventually_cofinite_notMem
  rw [Nat.cofinite_eq_atTop] at avoid
  filter_upwards [avoid] with i outsider
  obtain ⟨high,lo,fail⟩ := bad i
  have jp : (0:ℝ)<J i := by exact_mod_cast (show 0<J i by omega)
  by_contra! small
  exact outsider ⟨high,lo,(div_le_iff₀ jp).mp small.le,fail⟩

#print axioms finite_exceptional_rows
#print axioms exceptional_ratio_tendsto
end OrderedPartitions
