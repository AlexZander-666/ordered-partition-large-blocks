import OrderedPartitions.HardRodRightBrackets
import Mathlib.Data.Multiset.Sort

/-! A family with adjacent rightward motion needs only its longest comparison
to certify every intervening shift. Roots are indexed from the right. -/
noncomputable section
namespace OrderedPartitions.RootTracking
open Polynomial InterlacingStep

def rootFromRight (p : ℝ[X]) (k : ℕ) : ℝ :=
  ((p.roots.sort (· ≤ ·))[p.natDegree-(k+1)]?).getD 0

theorem rootFromRight_eq {p : ℝ[X]} {d : ℕ} {xs : Fin d → ℝ}
    (hp : RootArray p xs) {k : ℕ} (hk : k < d) :
    rootFromRight p k = xs ⟨d-(k+1), by omega⟩ := by
  have eqn : p.roots.sort (· ≤ ·) = List.ofFn xs := by
    apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort ..) hp.ordered.monotone.sortedLE_ofFn.pairwise
    apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq, hp.exact.roots]
  simp [rootFromRight,eqn,hp.degree,show d-(k+1)<d by omega]

theorem orderedPair_right_motion {p q : ℝ[X]} {d : ℕ} (pair : OrderedPair d p q)
    {k : ℕ} (hk : k<d) : rootFromRight p k < rootFromRight q k := by
  obtain ⟨xs,hp,⟨ys,hq,ord⟩|⟨ys,hq,ord⟩⟩ := pair
  · rw [rootFromRight_eq hp hk,rootFromRight_eq hq hk]
    exact ord.1 _
  · rw [rootFromRight_eq hp hk,rootFromRight_eq hq (by omega : k<d+1)]
    let i : Fin d := ⟨d-(k+1),by omega⟩
    have eqn : i.succ = (⟨d+1-(k+1),by omega⟩ : Fin (d+1)) := Fin.ext (by dsimp [i];omega)
    exact eqn ▸ (ord i).2

theorem orderedPair_right_gap {p q : ℝ[X]} {d : ℕ} (pair : OrderedPair d p q)
    {k : ℕ} (hk : k<d) (room : k+1<q.natDegree) :
    rootFromRight q (k+1) < rootFromRight p k := by
  obtain ⟨xs,hp,⟨ys,hq,ord⟩|⟨ys,hq,ord⟩⟩ := pair
  · rw [hq.degree] at room
    rw [rootFromRight_eq hp hk,rootFromRight_eq hq room]
    exact ord.2 _ _ (by change d-(k+1+1)<d-(k+1);omega)
  · rw [hq.degree] at room
    rw [rootFromRight_eq hp hk,rootFromRight_eq hq room]
    let i : Fin d := ⟨d-(k+1),by omega⟩
    have eqn : i.castSucc = (⟨d+1-(k+1+1),by omega⟩ : Fin (d+1)) :=
      Fin.ext (by dsimp [i];omega)
    exact eqn ▸ (ord i).1

theorem orderedPair_of_right_ranks {p q : ℝ[X]} {d e : ℕ} {xs : Fin d → ℝ}
    {ys : Fin e → ℝ} (hp : RootArray p xs) (hq : RootArray q ys) (deg : e=d ∨ e=d+1)
    (move : ∀ k<d, rootFromRight p k < rootFromRight q k)
    (gap : ∀ k<d, k+1<e → rootFromRight q (k+1) < rootFromRight p k) :
    OrderedPair d p q := by
  rcases deg with rfl|rfl
  · refine ⟨xs,hp,Or.inl ⟨ys,hq,?_,?_⟩⟩
    · intro i
      let k := e-(i.val+1)
      have ki : k < e := by dsimp [k]; omega
      have id : (⟨e-(k+1),by omega⟩ : Fin e) = i := Fin.ext (by dsimp [k];omega)
      simpa only [rootFromRight_eq hp ki,rootFromRight_eq hq ki,id] using move k ki
    · intro i j ij
      let k := e-(j.val+1)
      have ki : k < e := by dsimp [k]; omega
      have k1 : k+1 < e := by dsimp [k]; omega
      have id : (⟨e-(k+1),by omega⟩ : Fin e) = j := Fin.ext (by dsimp [k];omega)
      have near := gap k ki k1
      rw [rootFromRight_eq hp ki,rootFromRight_eq hq k1,id] at near
      exact (hq.ordered.monotone (show i ≤ (⟨e-(k+1+1),by omega⟩ : Fin e) by
        change i.val ≤ e-(k+1+1);dsimp [k];omega)).trans_lt near
  · refine ⟨xs,hp,Or.inr ⟨ys,hq,?_⟩⟩
    intro i
    let k := d-(i.val+1)
    have ki : k<d := by dsimp [k];omega
    have k0 : k<d+1 := by omega
    have k1 : k+1<d+1 := by omega
    have i0 : (⟨d-(k+1),by omega⟩ : Fin d)=i := Fin.ext (by dsimp [k];omega)
    have uc : (⟨d+1-(k+1+1),by omega⟩ : Fin (d+1))=i.castSucc :=
      Fin.ext (by dsimp [k];omega)
    have us : (⟨d+1-(k+1),by omega⟩ : Fin (d+1))=i.succ :=
      Fin.ext (by dsimp [k];omega)
    exact ⟨by simpa only [rootFromRight_eq hp ki,rootFromRight_eq hq k1,uc,i0] using gap k ki k1,
      by simpa only [rootFromRight_eq hp ki,rootFromRight_eq hq k0,us,i0] using move k ki⟩

/-- Adjacent root arrays determine strict rightward motion over any intermediate
number of steps, including each degree jump. -/
theorem rootFromRight_steps {P : ℕ → ℝ[X]} {J a b k : ℕ}
    (deg : Monotone fun u ↦ (P u).natDegree)
    (steps : ∀ u<J, OrderedPair (P u).natDegree (P u) (P (u+1)))
    (ab : a<b) (endpt : b≤J) (room : k<(P a).natDegree) :
    rootFromRight (P a) k < rootFromRight (P b) k := by
  have rest (v : ℕ) (av : a+1≤v) : v≤J →
      rootFromRight (P (a+1)) k ≤ rootFromRight (P v) k := by
    induction v, av using Nat.le_induction with
    | base => exact fun _ ↦ le_rfl
    | succ v av ih =>
      intro bound
      exact (ih (by omega)).trans (orderedPair_right_motion (steps v (by omega))
        (room.trans_le (deg (show a≤v by omega)))).le
  exact (orderedPair_right_motion (steps a (by omega)) room).trans_le (rest b ab endpt)

/-- A full-period comparison plus adjacent rightward motion implies every
shorter comparison, in the orientation of the actual polynomial roots. -/
theorem orderedPair_window_of_period {P : ℕ → ℝ[X]} {J h : ℕ}
    (deg : Monotone fun u ↦ (P u).natDegree)
    (steps : ∀ u<J, OrderedPair (P u).natDegree (P u) (P (u+1)))
    (width : (P J).natDegree ≤ (P 0).natDegree+1)
    (period : OrderedPair (P 0).natDegree (P 0) (P J)) (hh : 1≤h) (hj : h≤J) :
    OrderedPair (P 0).natDegree (P 0) (P h) := by
  by_cases final : h=J
  · simpa [final] using period
  have short : h<J := by omega
  have endperiod := period
  obtain ⟨xs,hp,_⟩ := endperiod
  obtain ⟨ys,hq,_⟩ := steps h short
  have d0 : (P 0).natDegree ≤ (P h).natDegree := deg (Nat.zero_le h)
  have d1 : (P h).natDegree ≤ (P 0).natDegree+1 := (deg hj).trans width
  apply orderedPair_of_right_ranks hp hq (by omega)
  · intro k hk
    exact rootFromRight_steps deg steps (by omega) hj hk
  · intro k hk room
    have left := rootFromRight_steps deg steps short le_rfl room
    have edge := orderedPair_right_gap period hk (room.trans_le (deg hj))
    exact left.trans edge

#print axioms orderedPair_window_of_period
#print axioms orderedPair_right_gap
end OrderedPartitions.RootTracking
