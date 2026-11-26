import OrderedPartitions.QuadraticActual
import OrderedPartitions.QuadraticRootOrder

noncomputable section
open Polynomial
namespace OrderedPartitions.QuadraticOrder

def rootMap (D y : ℝ) := 1+y/D

private theorem rootMap_increasing {D : ℝ} (hD : 0<D) : StrictMono (rootMap D) := by
  intro x y h
  dsimp [rootMap]
  linarith [div_lt_div_of_pos_right h hD]

private def factors (xs : List ℝ) : ℝ[X] := (xs.map (fun z ↦ X-C z)).prod

private theorem factors_monic (xs : List ℝ) : (factors xs).Monic := by
  induction xs with
  | nil => exact monic_one
  | cons x xs ih => exact (monic_X_sub_C x).mul ih

private theorem factors_roots (xs : List ℝ) : (factors xs).roots = (xs : Multiset ℝ) := by
  simpa [factors] using roots_multiset_prod_X_sub_C (xs : Multiset ℝ)

private theorem factors_affine (xs : List ℝ) {D : ℝ} (hD : 0<D) (t : ℝ) :
    (factors xs).eval (D*(t-1)) =
      D^xs.length*(factors (xs.map (rootMap D))).eval t := by
  induction xs with
  | nil => simp [factors]
  | cons x xs ih =>
    change ((X-C x)*factors xs).eval _ = _ * ((X-C (rootMap D x))*factors _).eval _
    rw [eval_mul,eval_mul,ih]
    simp only [eval_sub,eval_X,eval_C,List.length_cons,pow_succ,rootMap]
    field_simp
    ring

theorem ExactRoots.affine {p P : ℝ[X]} {xs : List ℝ} (roots : ExactRoots p xs)
    {D u : ℝ} (hD : 0<D) (hu : 0<u) (pn : p≠0)
    (evals : ∀t, P.eval t=u*p.eval (D*(t-1))) : ExactRoots P (xs.map (rootMap D)) := by
  let b := u*p.leadingCoeff*D^xs.length
  have bn : b≠0 := mul_ne_zero (mul_ne_zero hu.ne' (leadingCoeff_ne_zero.mpr pn)) (pow_ne_zero _ hD.ne')
  have eqn : P = C b * factors (xs.map (rootMap D)) := by
    apply Polynomial.funext
    intro t
    rw [evals, show p.eval (D*(t-1))=p.leadingCoeff*(factors xs).eval (D*(t-1)) by
      conv_lhs => rw [roots.factor]
      rw [eval_mul, eval_C]
      rfl]
    rw [factors_affine xs hD,eval_mul,eval_C]
    dsimp [b]
    ring
  refine ⟨?_,?_⟩
  · rw [eqn,roots_C_mul _ bn,factors_roots]
  · have lc : P.leadingCoeff=b := by rw [eqn,leadingCoeff_mul,leadingCoeff_C,(factors_monic _).leadingCoeff, mul_one]
    rw [lc]
    exact eqn

private theorem image_negative {P : ℝ[X]} {xs : List ℝ} (h : ExactRoots P xs) {x : ℝ}
    (hx : x ∈ xs) (positive : ∀ t, 0≤t → 0<P.eval t) : x<0 := by
  by_contra! no
  have mr : x ∈ P.roots := by rw [h.roots]; exact hx
  exact (positive _ no).ne' (isRoot_of_mem_roots mr)

theorem adjacent_affine {p q P Q : ℝ[X]} {D u v : ℝ} {jump : Prop}
    (hD : 0<D) (hu : 0<u) (hv : 0<v) (pn : p≠0) (qn : q≠0)
    (ep : ∀t, P.eval t=u*p.eval (D*(t-1))) (eq : ∀t, Q.eval t=v*q.eval (D*(t-1)))
    (positive : ∀t, 0≤t → 0<Q.eval t) (h : Adjacent p q jump) : Adjacent P Q jump := by
  have mono := rootMap_increasing hD
  rcases h with ⟨jump,a,b,c,d,e,hab,hbc,hcd,hde,_,hp,hq⟩ | ⟨stay,a,b,c,d,hab,hbc,hcd,_,hp,hq⟩
  · have rp := hp.affine hD hu pn ep
    have rq := hq.affine hD hv qn eq
    exact Or.inl ⟨jump,_,_,_,_,_,mono hab,mono hbc,mono hcd,mono hde,
      image_negative rq (by simp) positive, rp, rq⟩
  · have rp := hp.affine hD hu pn ep
    have rq := hq.affine hD hv qn eq
    exact Or.inr ⟨stay,_,_,_,_,mono hab,mono hbc,mono hcd,
      image_negative rq (by simp) positive, rp, rq⟩

theorem original_positive {j : ℕ} (hj : 2≤j) (n : ℕ) {t : ℝ} (ht : 0≤t) :
    0<(row n j).eval t := by
  rw [row, eval_finsetSum]
  simp only [eval_mul,eval_C,eval_pow,eval_X]
  have term := Finset.single_le_sum (s:=Finset.range (n+1))
    (f:=fun d ↦ (count n j d:ℝ)*t^d) (fun i _ ↦ by positivity)
    (Finset.mem_range.mpr (by omega : 0<n+1))
  simp only [pow_zero,mul_one] at term
  exact lt_of_lt_of_le (by exact_mod_cast count_zero_positive n hj) term

open Kernel

theorem original_adjacent_of_normalized {j n : ℕ} (hj : 2≤j) (hn : n<3*j)
    (normalized : Adjacent
      (quadratic 1 (normalizedMoment n j 1) (normalizedMoment n j 2))
      (cubic 1 (normalizedMoment (n+1) j 1) (normalizedMoment (n+1) j 2)
        (normalizedMoment (n+1) j 3)) (0<normalizedMoment (n+1) j 3)) :
    Adjacent (row n j) (row (n+1) j) (n+1=3*j) := by
  have j1 : 1≤j := by omega
  have jpos := markScale_pos j
  have low := normalized_before j1 hn
  have jump : (0<normalizedMoment (n+1) j 3) ↔ n+1=3*j := by
    constructor
    · intro hc
      by_contra ne
      rw [normalized_before j1 (by omega)] at hc
      exact lt_irrefl _ hc
    · intro e
      rw [e,normalized_cubic_at j1]
      have rp : 0<rho := by linarith [rho_interval.1]
      exact div_pos (by positivity) (k_pos _)
  rw [← jump]
  apply adjacent_affine (D:=markScale j) jpos (original_eval_pos j1 n)
    (original_eval_pos j1 (n+1)) _ _ _ _ (fun _ ht ↦ original_positive hj (n+1) ht) normalized
  · intro h
    have z := congrArg (Polynomial.eval 0) h
    simp at z
  · intro h
    have z := congrArg (Polynomial.eval 0) h
    simp at z
  · intro t
    have idn := original_eval_normalized j1 (show n<4*j by omega) t
    simpa [low] using idn
  · intro t
    simpa using original_eval_normalized j1 (show n+1<4*j by omega) t

#print axioms original_adjacent_of_normalized
#print axioms adjacent_affine
#print axioms original_positive
end OrderedPartitions.QuadraticOrder
