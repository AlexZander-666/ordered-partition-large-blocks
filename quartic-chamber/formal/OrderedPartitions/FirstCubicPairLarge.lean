import OrderedPartitions.FirstCubicPairMesh

noncomputable section
open Polynomial
namespace OrderedPartitions.QuadraticOrder
open Kernel

theorem three_affine {p q P Q : ℝ[X]} {D u v : ℝ}
    (hD : 0<D) (hu : 0<u) (hv : 0<v) (pn : p≠0) (qn : q≠0)
    (ep : ∀t, P.eval t=u*p.eval (D*(t-1))) (eq : ∀t, Q.eval t=v*q.eval (D*(t-1)))
    (positive : ∀t, 0≤t → 0<Q.eval t) (h : ThreeToThree p q) : ThreeToThree P Q := by
  rcases h with ⟨a,b,c,d,e,f,ab,bc,cd,de,ef,_,hp,hq⟩
  have rp := hp.affine hD hu pn ep
  have rq := hq.affine hD hv qn eq
  have mono : StrictMono (rootMap D) := by
    intro x y xy
    dsimp [rootMap]
    linarith [div_lt_div_of_pos_right xy hD]
  have neg : rootMap D f<0 := by
    by_contra! no
    have z : rootMap D f ∈ Q.roots := by rw [rq.roots]; simp
    exact (positive _ no).ne' (isRoot_of_mem_roots z)
  exact ⟨_,_,_,_,_,_,mono ab,mono bc,mono cd,mono de,mono ef,neg,rp,rq⟩

theorem original_first_cubic_large {j : ℕ} (hj : 50≤j) :
    ThreeToThree (row (3*j) j) (row (3*j+1) j) := by
  let n := 3*j
  let a := normalizedMoment n j 1
  let b := normalizedMoment n j 2
  let c := normalizedMoment n j 3
  let A := normalizedMoment (n+1) j 1
  let B := normalizedMoment (n+1) j 2
  let C := normalizedMoment (n+1) j 3
  let d := A-a
  let e := B-b
  let f := C-c
  let p := cubic 1 a b c
  let q := cubic 1 A B C
  have j1 : 1≤j := by omega
  have j2 : 2≤j := by omega
  have J : (50:ℝ)≤j := by exact_mod_cast hj
  have inputs := original_quadratic_estimates hj j
  dsimp only at inputs
  rw [show 2*j+j=n by dsimp [n]; omega] at inputs
  obtain ⟨al,au,dl,du,bl,bu,el,eu⟩ := inputs
  have bL : 0.49*(j:ℝ)^2 ≤ b := by
    change _ ≤ normalizedMoment n j 2
    nlinarith
  have bU : b ≤ 0.607*(j:ℝ)^2 := by
    have h : (j:ℝ)+4 ≤ 1.08*j := by linarith
    have s := pow_le_pow_left₀ (show (0:ℝ)≤j+4 by positivity) h 2
    change normalizedMoment n j 2 ≤ _
    nlinarith [sq_nonneg (j:ℝ)]
  obtain ⟨cl,cu⟩ := cubic_entry_bounds j2
  obtain ⟨fl,fu⟩ := cubic_increment_bounds j2
  have ff : f < 9 := fu.mpr (by omega)
  have roots := first_cubic_mesh (a:=a) (b:=b) (c:=c) (d:=d) (e:=e) (f:=f) J
    (by change _ ≤ normalizedMoment n j 1; linarith)
    (by change normalizedMoment n j 1 ≤ _; linarith)
    bL bU (by change 3≤normalizedMoment (3*j) j 3; linarith)
    (by change normalizedMoment (3*j) j 3≤4; linarith) dl du el
    (by change normalizedMoment (n+1) j 2-normalizedMoment n j 2≤_; linarith)
    (by change 4≤normalizedMoment (3*j+1) j 3-normalizedMoment (3*j) j 3; linarith) (by linarith)
  have pq : ThreeToThree p q := by simpa only [p,q,d,e,f,add_sub_cancel] using roots
  have pN : p≠0 := by intro z; have h := congrArg (Polynomial.eval 0) z; simp [p] at h
  have qN : q≠0 := by intro z; have h := congrArg (Polynomial.eval 0) z; simp [q] at h
  exact three_affine (D:=markScale j) (u:=(row n j).eval 1) (v:=(row (n+1) j).eval 1)
    (markScale_pos j) (original_eval_pos j1 _) (original_eval_pos j1 _) pN qN
    (fun t ↦ by simpa [p,a,b,c] using original_eval_normalized j1 (show n<4*j by dsimp [n]; omega) t)
    (fun t ↦ by simpa [q,A,B,C] using original_eval_normalized j1 (show n+1<4*j by dsimp [n]; omega) t)
    (fun _ ht ↦ original_positive j2 _ ht) pq

#print axioms three_affine
#print axioms original_first_cubic_large
end OrderedPartitions.QuadraticOrder
