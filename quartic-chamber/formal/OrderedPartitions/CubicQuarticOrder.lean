import OrderedPartitions.CubicChamberSeparation
import Mathlib.Analysis.Polynomial.Basic

/-! Complete root lists for the cubic plateau and the transition to degree four. -/
noncomputable section
open Polynomial Filter
namespace OrderedPartitions.QuadraticOrder

/-- Strict alternation through the first quartic, including the new leftmost zero. -/
def ThreeToFour (p q : ℝ[X]) : Prop :=
  ∃ A a B b C c D : ℝ, A<a ∧ a<B ∧ B<b ∧ b<C ∧ C<c ∧ c<D ∧ D<0 ∧
    ExactRoots p [a,b,c] ∧ ExactRoots q [A,B,C,D]

/-- Reflection converts both signs at negative infinity to standard atTop results. -/
private theorem left_probe (p : ℝ[X]) {n : ℕ} (deg : p.natDegree=n) (hn : 0<n)
    (lc : 0 < p.leadingCoeff) (a : ℝ) :
    (Even n → ∃ x<a, 0<p.eval x) ∧ (Odd n → ∃ x<a, p.eval x<0) := by
  let t := p.comp (-X)
  have td : 0<t.degree := natDegree_pos_iff_degree_pos.mp (by simpa [t,natDegree_comp,deg] using hn)
  have lead : t.leadingCoeff = p.leadingCoeff * (-1)^n := by
    simp [t, leadingCoeff_comp (show (-X : ℝ[X]).natDegree≠0 by simp),deg]
  have val (y : ℝ) : t.eval y = p.eval (-y) := by simp [t,eval_comp]
  constructor
  · intro even
    have pos : 0 ≤ t.leadingCoeff := by rw [lead,even.neg_one_pow,mul_one]; exact lc.le
    have ev := (t.tendsto_atTop_of_leadingCoeff_nonneg td pos).eventually (eventually_gt_atTop (0:ℝ))
    obtain ⟨y,hy,ey⟩ := ((eventually_gt_atTop (-a)).and ev).exists
    exact ⟨-y, by linarith, (val y) ▸ ey⟩
  · intro odd
    have neg : t.leadingCoeff ≤ 0 := by rw [lead,odd.neg_one_pow,mul_neg_one]; linarith
    have ev := (t.tendsto_atBot_of_leadingCoeff_nonpos td neg).eventually (eventually_lt_atBot (0:ℝ))
    obtain ⟨y,hy,ey⟩ := ((eventually_gt_atTop (-a)).and ev).exists
    exact ⟨-y, by linarith, (val y) ▸ ey⟩

/-- The degree increase specifies the complete root order for both polynomials. -/
def CubicAdjacent (p q : ℝ[X]) (jump : Prop) : Prop :=
  (jump ∧ ThreeToFour p q) ∨ (¬jump ∧ ThreeToThree p q)

private theorem between_up {p : ℝ[X]} {a b : ℝ} (h : a<b) (a0 : p.eval a<0) (b0 : 0<p.eval b) :
    ∃ x, a<x ∧ x<b ∧ p.eval x=0 := by
  obtain ⟨x,⟨l,r⟩,z⟩ := intermediate_value_Ioo h.le p.continuous.continuousOn
    (show 0 ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨a0,b0⟩)
  exact ⟨x,l,r,z⟩

private theorem between_down {p : ℝ[X]} {a b : ℝ} (h : a<b) (a0 : 0<p.eval a) (b0 : p.eval b<0) :
    ∃ x, a<x ∧ x<b ∧ p.eval x=0 := by
  obtain ⟨x,⟨l,r⟩,z⟩ := intermediate_value_Ioo' h.le p.continuous.continuousOn
    (show 0 ∈ Set.Ioo (p.eval b) (p.eval a) from ⟨b0,a0⟩)
  exact ⟨x,l,r,z⟩

private theorem exact_four {p : ℝ[X]} {a b c d : ℝ} (pn : p≠0) (deg : p.natDegree≤4)
    (ab : a<b) (bc : b<c) (cd : c<d) (pa : p.eval a=0) (pb : p.eval b=0)
    (pc : p.eval c=0) (pd : p.eval d=0) : ExactRoots p [a,b,c,d] := by
  classical
  let xs := [a,b,c,d]
  have nd : xs.Nodup := by simp [xs,ab.ne,bc.ne,cd.ne,(ab.trans bc).ne,(bc.trans cd).ne,((ab.trans bc).trans cd).ne]
  have hd : p.natDegree≤xs.length := deg
  have card := List.toFinset_card_of_nodup nd
  have idr := roots_eq_of_natDegree_le_card_of_ne_zero (S:=xs.toFinset) (p:=p)
    (fun x hx ↦ by
      have h := List.mem_toFinset.mp hx
      simp only [xs,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl <;> assumption) (by rwa [card]) pn
  have rm : p.roots=(xs : Multiset ℝ) := by rw [idr,List.toFinset_val,List.dedup_eq_self.mpr nd]
  have sp := splits_iff_card_roots.mpr (le_antisymm p.card_roots' (by simpa [rm] using hd))
  exact ⟨rm,by simpa [rm,xs] using sp.eq_prod_roots⟩

/-- Alternating signs at the old roots produce all four new roots when the leading
quartic coefficient is positive. -/
theorem three_to_four_of_signs {p q : ℝ[X]} {a b c : ℝ} (hp : ExactRoots p [a,b,c])
    (ab : a<b) (bc : b<c) (c0 : c<0) (qa : q.eval a<0) (qb : 0<q.eval b)
    (qc : q.eval c<0) (q0 : 0<q.eval 0) (qd : q.natDegree=4) (ql : 0<q.leadingCoeff) :
    ThreeToFour p q := by
  obtain ⟨x,xa,qx⟩ := (left_probe q qd (by decide) ql a).1 (by decide)
  obtain ⟨A,_,Aa,hA⟩ := between_down xa qx qa
  obtain ⟨B,aB,Bb,hB⟩ := between_up ab qa qb
  obtain ⟨C,bC,Cc,hC⟩ := between_down bc qb qc
  obtain ⟨D,cD,D0,hD⟩ := between_up c0 qc q0
  have qn : q≠0 := fun h ↦ q0.ne' (by simp [h])
  exact ⟨A,a,B,b,C,c,D,Aa,aB,Bb,bC,Cc,cD,D0,hp,
    exact_four qn qd.le (Aa.trans aB) (Bb.trans bC) (Cc.trans cD) hA hB hC hD⟩

/-- Two roots of the quadratic difference separate all the roots of the old cubic.
The resulting sign test works both before and at the degree increase. -/
theorem cubic_adjacent_at_points {p q : ℝ[X]} {jump : Prop} {w z f : ℝ}
    (pd : p.natDegree=3) (pl : 0<p.leadingCoeff) (p0 : 0<p.eval 0)
    (q0 : 0<q.eval 0) (noJump : ¬jump → q.natDegree≤3)
    (atJump : jump → q.natDegree=4 ∧ 0<q.leadingCoeff)
    (wp : 0<w) (wz : w<z) (fp : 0<f) (atFar : 0<p.eval (-z)) (atNear : p.eval (-w)<0)
    (rem : ∀ x : ℝ, p.eval x=0 → q.eval x=x*(f*(x+w)*(x+z))) :
    CubicAdjacent p q jump := by
  obtain ⟨x,xz,px⟩ := (left_probe p pd (by decide) pl (-z)).2 (by decide)
  obtain ⟨a,_,az,pa⟩ := between_up xz px atFar
  obtain ⟨b,zb,bw,pb⟩ := between_down (neg_lt_neg wz) atFar atNear
  obtain ⟨c,wc,c0,pc⟩ := between_up (neg_lt_zero.mpr wp) atNear p0
  have ab := az.trans zb
  have bc := bw.trans wc
  have pn : p≠0 := fun h ↦ p0.ne' (by simp [h])
  have hp := exact_three pn pd.le ab bc pa pb pc
  have qa : q.eval a<0 := by
    rw [rem a pa]
    apply mul_neg_of_neg_of_pos (ab.trans (bc.trans c0))
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg fp (by linarith)) (by linarith)
  have qb : 0<q.eval b := by
    rw [rem b pb]
    apply mul_pos_of_neg_of_neg (bc.trans c0)
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg fp (by linarith)) (by linarith)
  have qc : q.eval c<0 := by
    rw [rem c pc]
    exact mul_neg_of_neg_of_pos c0 (mul_pos (mul_pos fp (by linarith)) (by linarith))
  by_cases h : jump
  · exact Or.inl ⟨h,three_to_four_of_signs hp ab bc c0 qa qb qc q0 (atJump h).1 (atJump h).2⟩
  · exact Or.inr ⟨h,threeToThree_of_signs hp ab bc c0 qa qb qc q0 (noJump h)⟩

#print axioms cubic_adjacent_at_points
#print axioms three_to_four_of_signs
#print axioms left_probe
end OrderedPartitions.QuadraticOrder
