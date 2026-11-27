import OrderedPartitions.HardRodStableDegree
import Mathlib.Topology.Sequences

namespace OrderedPartitions.RootTracking
open Filter Set
open scoped Topology

/-- Compactness in a closed chamber. Both integral endpoints are included in
the subsequential hypothesis; the upper rank bound at finite n is strict. -/
theorem uniform_chamber_of_limits (good : ℕ→ℕ→Prop) (D : ℕ)
    (at_limit : ∀ {J N : ℕ→ℕ} {x : ℝ}, (D:ℝ)≤x → x≤(D:ℝ)+1 →
      Tendsto J atTop atTop → Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x) →
      (∀ i,D*J i≤N i ∧ N i<(D+1)*J i) → ∀ᶠ i in atTop, good (J i) (N i)) :
    ∃ K, ∀ j≥K, ∀ n, D*j≤n → n<(D+1)*j → good j n := by
  by_contra! fail
  choose J large N lo hi bad using fun i ↦ fail (i+2)
  have diverge : Tendsto J atTop atTop := tendsto_atTop_mono (fun i ↦ by
    exact (Nat.le_add_right i 2).trans (large i)) tendsto_id
  have bounds (i) : (N i:ℝ)/(J i:ℝ) ∈ Icc (D:ℝ) ((D:ℝ)+1) := by
    have jp : 0<(J i:ℝ) := by exact_mod_cast (show 0<J i by have := large i;omega)
    exact ⟨(le_div_iff₀ jp).mpr (by exact_mod_cast lo i),
      (div_le_iff₀ jp).mpr (by exact_mod_cast (hi i).le)⟩
  obtain ⟨x,hx,φ,inc,con⟩ := isCompact_Icc.tendsto_subseq bounds
  have ok := at_limit (J:=J ∘ φ) (N:=N ∘ φ) hx.1 hx.2 (diverge.comp inc.tendsto_atTop)
    con (fun i ↦ ⟨lo _,hi _⟩)
  obtain ⟨i,positive⟩ := ok.exists
  exact bad (φ i) positive

/-- The finitely many rank chambers below any given real ratio C admit one
eventual cutoff, even when neither the number nor the thresholds are explicit. -/
theorem uniform_ratio_of_chambers (good : ℕ→ℕ→Prop)
    (each : ∀ D : ℕ, 1≤D → ∃ K, ∀ j≥K, ∀ n, D*j≤n → n<(D+1)*j → good j n)
    (C : ℝ) : ∃ K : ℕ, ∀ j : ℕ, K≤j → ∀ n : ℕ, j≤n → (n:ℝ)≤C*(j:ℝ) → good j n := by
  obtain ⟨L,CL⟩ := exists_nat_ge C
  classical
  choose thresholds hs using fun D : ℕ ↦ each (D+1) (by omega)
  let K := (Finset.range (L+1)).sup thresholds + 1
  refine ⟨K,?_⟩
  intro j hj n jn ceiling
  have jp : 0<j := by dsimp [K] at hj;omega
  have ub : n≤L*j := by exact_mod_cast (ceiling.trans (mul_le_mul_of_nonneg_right CL (Nat.cast_nonneg j)))
  have Dlo : 1≤n/j := by rw [Nat.le_div_iff_mul_le jp]; simpa using jn
  have Dup : n/j≤L := (Nat.div_le_div_right ub).trans (by simp [Nat.mul_div_cancel _ jp])
  let D := n/j-1
  have vv : D+1=n/j := by dsimp [D];omega
  have small : thresholds D≤(Finset.range (L+1)).sup thresholds :=
    Finset.le_sup (f:=thresholds) (Finset.mem_range.mpr (show D<L+1 by dsimp [D];omega))
  apply hs D j (small.trans (by dsimp [K] at hj;omega)) n
  · rw [vv];exact Nat.div_mul_le_self _ _
  · rw [vv]
    exact (Nat.div_lt_iff_lt_mul jp).mp (Nat.lt_succ_self _)

#print axioms uniform_chamber_of_limits
#print axioms uniform_ratio_of_chambers
end OrderedPartitions.RootTracking
