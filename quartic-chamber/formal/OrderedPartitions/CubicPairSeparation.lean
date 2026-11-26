import OrderedPartitions.QuadraticTransport

noncomputable section
open Polynomial
namespace OrderedPartitions.QuadraticOrder

def ThreeToThree (p q : ℝ[X]) : Prop :=
  ∃ r₁ s₁ r₂ s₂ r₃ s₃ : ℝ,
    r₁<s₁ ∧ s₁<r₂ ∧ r₂<s₂ ∧ s₂<r₃ ∧ r₃<s₃ ∧ s₃<0 ∧
    ExactRoots p [r₁,r₂,r₃] ∧ ExactRoots q [s₁,s₂,s₃]

private theorem ivt_up (p : ℝ[X]) {a b : ℝ} (lt : a<b) (neg : p.eval a<0) (pos : 0<p.eval b) :
    ∃x, a<x ∧ x<b ∧ p.eval x=0 := by
  obtain ⟨x,h,z⟩ := intermediate_value_Ioo lt.le p.continuous.continuousOn
    (show (0:ℝ)∈Set.Ioo (p.eval a) (p.eval b) from ⟨neg,pos⟩)
  exact ⟨x,h.1,h.2,z⟩

private theorem ivt_down (p : ℝ[X]) {a b : ℝ} (lt : a<b) (pos : 0<p.eval a) (neg : p.eval b<0) :
    ∃x, a<x ∧ x<b ∧ p.eval x=0 := by
  obtain ⟨x,h,z⟩ := intermediate_value_Ioo' lt.le p.continuous.continuousOn
    (show (0:ℝ)∈Set.Ioo (p.eval b) (p.eval a) from ⟨neg,pos⟩)
  exact ⟨x,h.1,h.2,z⟩

theorem exact_three {p : ℝ[X]} {a b c : ℝ} (pn : p≠0) (deg : p.natDegree≤3)
    (ab : a<b) (bc : b<c) (pa : p.eval a=0) (pb : p.eval b=0) (pc : p.eval c=0) :
    ExactRoots p [a,b,c] := by
  classical
  let xs := [a,b,c]
  have nd : xs.Nodup := by simp [xs,ab.ne,bc.ne,(ab.trans bc).ne]
  have len : p.natDegree ≤ xs.length := deg
  have card := List.toFinset_card_of_nodup nd
  have idr := roots_eq_of_natDegree_le_card_of_ne_zero (S:=xs.toFinset)
    (p:=p) (fun x hx ↦ by
      have h := List.mem_toFinset.mp hx
      simp only [xs, List.mem_cons,List.mem_nil_iff,or_false] at h
      rcases h with rfl|rfl|rfl <;> assumption)
    (by rwa [card]) pn
  have rm : p.roots = (xs : Multiset ℝ) := by rw [idr,List.toFinset_val,List.dedup_eq_self.mpr nd]
  have split := splits_iff_card_roots.mpr (le_antisymm p.card_roots' (by simpa [rm] using len))
  exact ⟨rm,by simpa [rm,xs] using split.eq_prod_roots⟩

/-- Three old roots, three evaluations of the upper row, and its positive constant term
certify the complete strict order and multiplicities for a pair of cubic rows. -/
theorem three_to_three_at_roots {p q : ℝ[X]} (pd : p.natDegree≤3) (qd : q.natDegree≤3)
    (pn : p≠0) (q0 : 0<q.eval 0) {a b c : ℝ} (ab : a<b) (bc : b<c) (c0 : c<0)
    (pa : p.eval a=0) (pb : p.eval b=0) (pc : p.eval c=0)
    (qa : q.eval a<0) (qb : 0<q.eval b) (qc : q.eval c<0) : ThreeToThree p q := by
  have qn : q≠0 := fun e ↦ q0.ne' (by simp [e])
  obtain ⟨A,aA,Ab,qA⟩ := ivt_up q ab qa qb
  obtain ⟨B,bB,Bc,qB⟩ := ivt_down q bc qb qc
  obtain ⟨C,cC,C0,qC⟩ := ivt_up q c0 qc q0
  exact ⟨a,A,b,B,c,C,aA,Ab,bB,Bc,cC,C0,exact_three pn pd ab bc pa pb pc,
    exact_three qn qd (Ab.trans bB) (Bc.trans cC) qA qB qC⟩

theorem threeToThree_of_signs {p q : ℝ[X]} {a b c : ℝ} (hp : ExactRoots p [a,b,c])
    (ab : a<b) (bc : b<c) (c0 : c<0)
    (qa : q.eval a<0) (qb : 0<q.eval b) (qc : q.eval c<0)
    (q0 : 0<q.eval 0) (qd : q.natDegree≤3) : ThreeToThree p q := by
  have qn : q≠0 := fun e ↦ q0.ne' (by simp [e])
  obtain ⟨A,aA,Ab,qA⟩ := ivt_up q ab qa qb
  obtain ⟨B,bB,Bc,qB⟩ := ivt_down q bc qb qc
  obtain ⟨C,cC,C0,qC⟩ := ivt_up q c0 qc q0
  exact ⟨a,A,b,B,c,C,aA,Ab,bB,Bc,cC,C0,hp,
    exact_three qn qd (Ab.trans bB) (Bc.trans cC) qA qB qC⟩

private theorem quadratic_at_two_roots {d e f a b : ℝ} (ab : a<b)
    (za : (quadratic d e f).eval a=0) (zb : (quadratic d e f).eval b=0) (x : ℝ) :
    (quadratic d e f).eval x = f*(x-a)*(x-b) := by
  simp only [eval_quadratic] at *
  have z : (a-b)*(e+f*(a+b))=0 := by linear_combination za-zb
  have v := (mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr ab.ne)
  linear_combination za+(x-a)*v

/-- Four shared test points isolate alternating roots of the old cubic and the
quadratic divided difference (Q-P)/X. This only uses signs and degrees. -/
theorem divided_difference_mesh {P Q : ℝ[X]} {d e f : ℝ} (fpos : 0<f)
    (pd : P.natDegree≤3) (qd : Q.natDegree≤3) (p0 : 0<P.eval 0)
    (diff : ∀x, Q.eval x = P.eval x+x*(quadratic d e f).eval x)
    {t A B C D : ℝ} (tA : t<A) (aB : A<B) (bC : B<C) (cD : C<D) (d0 : D<0)
    (pt : P.eval t<0) (pA : 0<P.eval A) (pB : 0<P.eval B) (pC : P.eval C<0) (pD : P.eval D<0)
    (hA : 0<(quadratic d e f).eval A) (hB : (quadratic d e f).eval B<0)
    (hC : (quadratic d e f).eval C<0) (hD : 0<(quadratic d e f).eval D) : ThreeToThree P Q := by
  obtain ⟨a,_,aA,pa⟩ := ivt_up P tA pt pA
  obtain ⟨b,Bb,bC',pb⟩ := ivt_down P bC pB pC
  obtain ⟨c,Dc,c0,pc⟩ := ivt_up P d0 pD p0
  obtain ⟨l,Al,lB,hl⟩ := ivt_down _ aB hA hB
  obtain ⟨r,Cr,rD,hr⟩ := ivt_up _ cD hC hD
  have lr := lB.trans (bC.trans Cr)
  have al := aA.trans Al
  have lb := lB.trans Bb
  have br := bC'.trans Cr
  have rc := rD.trans Dc
  have pn : P≠0 := fun z ↦ p0.ne' (by simp [z])
  have q0 : 0<Q.eval 0 := by simpa [diff] using p0
  apply three_to_three_at_roots pd qd pn q0 (al.trans lb) (br.trans rc) c0 pa pb pc
  · rw [diff,pa,zero_add,quadratic_at_two_roots lr hl hr]
    have a0 := (al.trans (lr.trans rc)).trans c0
    exact mul_neg_of_neg_of_pos a0 (mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg fpos (sub_neg.mpr al)) (sub_neg.mpr (al.trans lr)))
  · rw [diff,pb,zero_add,quadratic_at_two_roots lr hl hr]
    exact mul_pos_of_neg_of_neg ((br.trans rc).trans c0)
      (mul_neg_of_pos_of_neg (mul_pos fpos (sub_pos.mpr lb)) (sub_neg.mpr br))
  · rw [diff,pc,zero_add,quadratic_at_two_roots lr hl hr]
    exact mul_neg_of_neg_of_pos c0
      (mul_pos (mul_pos fpos (sub_pos.mpr (lr.trans rc))) (sub_pos.mpr rc))

#print axioms threeToThree_of_signs
#print axioms three_to_three_at_roots
#print axioms divided_difference_mesh
end OrderedPartitions.QuadraticOrder
