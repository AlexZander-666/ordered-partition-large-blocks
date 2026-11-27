import OrderedPartitions.HardRodFiniteBranches
import OrderedPartitions.HardRodEntryGrowth

noncomputable section
namespace OrderedPartitions.RootTracking
open Filter Polynomial InterlacingStep Kernel HardRod
open scoped Topology

theorem window_shape {M j n D : ℕ} (hj : 2≤j) (pos : 1≤D) (cap : D≤M)
    (lo : D*j≤n) (hi : n<(D+1)*j) :
    (windowPoly M j n).natDegree=D ∧ 0<(windowPoly M j n).leadingCoeff ∧
    (windowPoly M j n).eval 0=1 := by
  have j1 : 1≤j := by omega
  have top : 0<(windowPoly M j n).coeff D := by
    obtain ⟨m,eq⟩ := Nat.exists_eq_add_of_le lo
    rw [windowPoly_coeff,if_pos cap,eq,add_comm]
    exact windowCoeff_positive hj pos m
  have deg : (windowPoly M j n).natDegree=D := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ top.ne'
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i h
    have before := markedCount_before (j:=j) (h:=i) j1 (hi.trans_le (Nat.mul_le_mul_right j h))
    simp [windowPoly_coeff,windowCoeff,normalizedMoment,before]
  exact ⟨deg,by simpa [leadingCoeff,deg] using top,by
    simp [← coeff_zero_eq_eval_zero,windowPoly_coeff,windowCoeff,normalizedMoment,markedCount_zero,
      (original_eval_pos j1 n).ne']⟩

/-- Includes the single degree increase when the upper rank reaches the next
multiple of j. The interval hypothesis only concerns the lower degree. -/
theorem normalized_stable_pair {J N : ℕ→ℕ} {x : ℝ} {d : ℕ}
    (lo : (d:ℝ)+1<x) (hi : x≤(d:ℝ)+2) (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun n ↦ (N n:ℝ)/(J n:ℝ)) atTop (𝓝 x))
    (rank : ∀ᶠ n in atTop,(d+1)*J n≤N n ∧ N n<(d+2)*J n) :
    ∀ᶠ n in atTop, OrderedPair (d+1) (windowPoly (d+2) (J n) (N n))
      (windowPoly (d+2) (J n) (N n+1)) := by
  obtain ⟨_,z,_,_,evt⟩ := finite_branches (M:=d+1) (Nat.le_succ d) lo hi hj hn
  filter_upwards [evt,rank,hj.eventually_ge_atTop 2] with n info rk big
  obtain ⟨sorted,tests⟩ := info
  have P := window_shape (M:=d+2) big (by omega : 1≤d+1) (by omega) rk.1 rk.2
  refine ⟨z n,⟨sorted,fun i ↦ (tests i).1,fun h ↦ ?_,P.1,fun i ↦ (tests i).2.1⟩,?_⟩
  · have hz := P.2.2
    simp [h] at hz
  · by_cases endRank : N n+1<(d+2)*J n
    · have Q := window_shape (M:=d+2) big (by omega : 1≤d+1) (by omega)
        (rk.1.trans (Nat.le_succ _)) endRank
      exact Or.inl (equal_of_alternating_sign sorted (fun i ↦ (tests i).1)
        (by linarith [Q.2.2]) Q.1 (fun i ↦ (tests i).2.2))
    · have equal : N n+1=(d+2)*J n := by omega
      have less : N n+1<(d+3)*J n := by rw [equal]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      have Q := window_shape (M:=d+2) big (by omega : 1≤d+2) (by omega) equal.ge less
      exact Or.inr (rise_of_alternating_sign sorted (fun i ↦ (tests i).1)
        Q.2.1 (by linarith [Q.2.2]) Q.1 (fun i ↦ (tests i).2.2))

#print axioms window_shape
#print axioms normalized_stable_pair
end OrderedPartitions.RootTracking
