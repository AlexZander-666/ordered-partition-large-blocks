import OrderedPartitions.CubicQuarticNormalized
import OrderedPartitions.FirstCubicPairLarge

/-! Transport of complete cubic and quartic root lists to the original ordered partitions. -/
noncomputable section
open Polynomial
namespace OrderedPartitions.Kernel

/-- The normalized Taylor expansion on the genuine labeled objects at any degree
bound. The same positive change of variable is used at all consecutive ranks. -/
theorem original_normalized_sum {n j h : ℕ} (hj : 1≤j) (hn : n<(h+1)*j) (t : ℝ) :
    (row n j).eval t = (row n j).eval 1 *
      ∑ i ∈ Finset.range (h+1), normalizedMoment n j i*(markScale j*(t-1))^i := by
  let p := (row n j).comp (X+1)
  have bound : p.natDegree≤h := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact markedCount_before hj (hn.trans_le (Nat.mul_le_mul_right j hi))
  have orig : p.eval (t-1)=(row n j).eval t := by simp [p,eval_comp]
  have scale := markScale_pos j
  have total := original_eval_pos hj n
  rw [← orig, eval_eq_sum_range' (Nat.lt_succ_iff.mpr bound),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change markedCount n j i*(t-1)^i = _
  simp only [normalizedMoment,mul_pow]
  field_simp

end OrderedPartitions.Kernel

namespace OrderedPartitions.QuadraticOrder
open Kernel

/-- The signs of original coefficients put the largest root to the left of zero
after the common positive change of variable. -/
theorem cubic_chamber_affine {p q P Q : ℝ[X]} {D u v : ℝ} {jump : Prop}
    (hD : 0<D) (hu : 0<u) (hv : 0<v) (pn : p≠0) (qn : q≠0)
    (ep : ∀t, P.eval t=u*p.eval (D*(t-1))) (eq : ∀t, Q.eval t=v*q.eval (D*(t-1)))
    (positive : ∀t, 0≤t → 0<Q.eval t) (h : CubicAdjacent p q jump) :
    CubicAdjacent P Q jump := by
  rcases h with ⟨yes,h₄⟩|⟨no,h₃⟩
  · left
    refine ⟨yes,?_⟩
    rcases h₄ with ⟨A,a,B,b,C,c,E,Aa,aB,Bb,bC,Cc,cE,_,hp,hq⟩
    have rp := hp.affine hD hu pn ep
    have rq := hq.affine hD hv qn eq
    have mono : StrictMono (rootMap D) := by
      intro x y xy
      dsimp [rootMap]
      linarith [div_lt_div_of_pos_right xy hD]
    have neg : rootMap D E<0 := by
      by_contra! z
      have mem : rootMap D E ∈ Q.roots := by rw [rq.roots]; simp
      exact (positive _ z).ne' (isRoot_of_mem_roots mem)
    exact ⟨_,_,_,_,_,_,_,mono Aa,mono aB,mono Bb,mono bC,mono Cc,mono cE,neg,rp,rq⟩
  · exact Or.inr ⟨no,three_affine hD hu hv pn qn ep eq positive h₃⟩

/-- The input is expressed on normalized moments, using the same variable for the
two ranks. The output is the complete root statement on labeled ordered partitions. -/
theorem original_cubic_chamber_of_normalized {n j : ℕ} (hj : 2≤j) (hn : n<4*j)
    (h : CubicAdjacent
      (cubic 1 (normalizedMoment n j 1) (normalizedMoment n j 2) (normalizedMoment n j 3))
      (quartic 1 (normalizedMoment (n+1) j 1) (normalizedMoment (n+1) j 2)
        (normalizedMoment (n+1) j 3) (normalizedMoment (n+1) j 4))
      (n+1=4*j)) : CubicAdjacent (row n j) (row (n+1) j) (n+1=4*j) := by
  let p := cubic 1 (normalizedMoment n j 1) (normalizedMoment n j 2) (normalizedMoment n j 3)
  let q := quartic 1 (normalizedMoment (n+1) j 1) (normalizedMoment (n+1) j 2)
    (normalizedMoment (n+1) j 3) (normalizedMoment (n+1) j 4)
  have j1 : 1≤j := by omega
  have p0 : p.eval 0=1 := by simp [p]
  have q0 : q.eval 0=1 := by simp [q]
  have e0 (r : ℕ) : normalizedMoment r j 0=1 := by
    simp [normalizedMoment, markedCount_zero,(original_eval_pos j1 r).ne']
  apply cubic_chamber_affine (p:=p) (q:=q) (markScale_pos j)
    (original_eval_pos j1 n) (original_eval_pos j1 (n+1))
    (fun z ↦ by simp [z] at p0) (fun z ↦ by simp [z] at q0) _ _
    (fun t ht ↦ original_positive hj (n+1) ht) h
  · intro t
    simpa [p,Finset.sum_range_succ,e0] using original_normalized_sum (h:=3) j1 hn t
  · intro t
    simpa [q,Finset.sum_range_succ,e0] using original_normalized_sum (h:=4) j1 (by omega : n+1<5*j) t

#print axioms original_cubic_chamber_of_normalized
#print axioms OrderedPartitions.Kernel.original_normalized_sum
#print axioms cubic_chamber_affine
end OrderedPartitions.QuadraticOrder
