import OrderedPartitions.HardRodPeriodOrder
import OrderedPartitions.HardRodRootTracking
import Mathlib.Algebra.Polynomial.FieldDivision

noncomputable section
namespace OrderedPartitions.RootTracking
open Filter Polynomial InterlacingStep
open scoped Topology

/-- Track every bounded simple root at once, allowing loss of degree at infinity. -/
theorem branches_of_complete_limit {P : ℕ → ℝ[X]} {p : ℝ[X]} {d : ℕ} {xs : Fin d → ℝ}
    (hp : RootArray p xs) (conv : ∀ x, Tendsto (fun n ↦ (P n).eval x) atTop (𝓝 (p.eval x))) :
    ∃ z : ℕ → Fin d → ℝ, (∀ i, Tendsto (fun n ↦ z n i) atTop (𝓝 (xs i))) ∧
      ∀ᶠ n in atTop, StrictMono (z n) ∧ ∀ i, z n i < 0 ∧ (P n).eval (z n i) = 0 := by
  classical
  have one (i : Fin d) : p.derivative.eval (xs i) ≠ 0 := by
    intro dh
    have bad := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp.ne_zero).mpr ⟨hp.zeros i,dh⟩
    have cap := Multiset.nodup_iff_count_le_one.mp hp.roots_nodup (xs i)
    rw [Polynomial.count_roots] at cap
    omega
  choose z lim zeros using fun i ↦ simple_branch conv (hp.zeros i) (one i)
  refine ⟨fun n i ↦ z i n, lim, ?_⟩
  have cp (i j : Fin d) : ∀ᶠ n in atTop, i<j → z i n<z j n := by
    by_cases h : i<j
    · exact ((lim i).eventually_lt (lim j) (hp.ordered h)).mono (fun _ lt _ ↦ lt)
    · exact .of_forall fun _ lt ↦ (h lt).elim
  have ord := eventually_all.mpr fun i ↦ eventually_all.mpr (cp i)
  have neg := eventually_all.mpr fun i ↦ ((lim i).eventually_lt_const (hp.negative i)).and (zeros i)
  filter_upwards [ord,neg] with n h₁ h₂
  exact ⟨fun i j ij ↦ h₁ i j ij,h₂⟩

/-- Stable degrees transport all strict intervals from a unit-separated limit
pair. Both rows may vary on the same sequence. -/
theorem period_of_stable_limit {P Q : ℕ → ℝ[X]} {p q : ℝ[X]} {d : ℕ}
    {xs : Fin d → ℝ} {ys : Fin (d+1) → ℝ}
    (hp : RootArray p xs) (hq : RootArray q ys) (sep : Interlaces xs ys)
    (cp : ∀ x, Tendsto (fun n ↦ (P n).eval x) atTop (𝓝 (p.eval x)))
    (cq : ∀ x, Tendsto (fun n ↦ (Q n).eval x) atTop (𝓝 (q.eval x)))
    (shape : ∀ᶠ n in atTop, P n≠0 ∧ (P n).natDegree=d ∧ Q n≠0 ∧ (Q n).natDegree=d+1) :
    ∀ᶠ n in atTop, OrderedPair d (P n) (Q n) := by
  obtain ⟨x,lx,px⟩ := branches_of_complete_limit hp cp
  obtain ⟨y,ly,qy⟩ := branches_of_complete_limit hq cq
  have cross := eventually_all.mpr fun i ↦
    ((ly i.castSucc).eventually_lt (lx i) (sep i).1).and
      ((lx i).eventually_lt (ly i.succ) (sep i).2)
  filter_upwards [px,qy,shape,cross] with n a b s c
  exact ⟨x n,⟨a.1,fun i ↦ (a.2 i).1,s.1,s.2.1,fun i ↦ (a.2 i).2⟩,
    Or.inr ⟨y n,⟨b.1,fun i ↦ (b.2 i).1,s.2.2.1,s.2.2.2,fun i ↦ (b.2 i).2⟩,c⟩⟩


/-- One additional root can disappear at minus infinity in each row. The
relative position of those two roots is the only extra rank comparison. -/
theorem period_of_lost_degree {P Q : ℕ → ℝ[X]} {p q : ℝ[X]} {d : ℕ}
    {xs : Fin d → ℝ} {ys : Fin (d+1) → ℝ}
    (hp : RootArray p xs) (hq : RootArray q ys) (sep : Interlaces xs ys)
    (cp : ∀ x, Tendsto (fun n ↦ (P n).eval x) atTop (𝓝 (p.eval x)))
    (cq : ∀ x, Tendsto (fun n ↦ (Q n).eval x) atTop (𝓝 (q.eval x)))
    (shape : ∀ᶠ n in atTop, P n≠0 ∧ (P n).natDegree=d+1 ∧ Q n≠0 ∧ (Q n).natDegree=d+2)
    (escape : ∀ T : ℝ, ∀ᶠ n in atTop, (∃ r<T, (P n).eval r=0) ∧ (∃ r<T, (Q n).eval r=0))
    (relative : ∀ᶠ n in atTop, ∀ (a : Fin (d+1) → ℝ) (b : Fin (d+2) → ℝ),
      RootArray (P n) a → RootArray (Q n) b → b 0 < a 0) :
    ∀ᶠ n in atTop, OrderedPair (d+1) (P n) (Q n) := by
  obtain ⟨x,lx,px⟩ := branches_of_complete_limit hp cp
  obtain ⟨y,ly,qy⟩ := branches_of_complete_limit hq cq
  let T := ys 0 - 1
  have Tneg : T<0 := by dsimp [T]; linarith [hq.negative 0]
  have sepY (i : Fin (d+1)) : T<ys i := by
    dsimp [T]; linarith [hq.ordered.monotone (Fin.zero_le i)]
  have sepX (i : Fin d) : T<xs i := (sepY _).trans (sep i).1
  have cross := eventually_all.mpr fun i ↦
    ((ly i.castSucc).eventually_lt (lx i) (sep i).1).and
      ((lx i).eventually_lt (ly i.succ) (sep i).2)
  filter_upwards [px,qy,shape,cross,escape T,relative,
    eventually_all.mpr fun i ↦ (lx i).eventually_const_lt (sepX i),
    eventually_all.mpr fun i ↦ (ly i).eventually_const_lt (sepY i)] with n a b sh c esc gap bx bys
  obtain ⟨⟨u,ut,uz⟩,v,vt,vz⟩ := esc
  let ax : Fin (d+1) → ℝ := Fin.cons u (x n)
  let ay : Fin (d+2) → ℝ := Fin.cons v (y n)
  have ra : RootArray (P n) ax := ⟨Fin.strictMono_cons.mpr ⟨fun i ↦ ut.trans (bx i),a.1⟩,
    Fin.cases (ut.trans Tneg) (fun i ↦ (a.2 i).1),sh.1,sh.2.1,
    Fin.cases uz (fun i ↦ (a.2 i).2)⟩
  have rb : RootArray (Q n) ay := ⟨Fin.strictMono_cons.mpr ⟨fun i ↦ vt.trans (bys i),b.1⟩,
    Fin.cases (vt.trans Tneg) (fun i ↦ (b.2 i).1),sh.2.2.1,sh.2.2.2,
    Fin.cases vz (fun i ↦ (b.2 i).2)⟩
  refine ⟨ax,ra,Or.inr ⟨ay,rb,?_⟩⟩
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · exact ⟨gap ax ay ra rb,ut.trans (bys 0)⟩
  · exact c k

#print axioms period_of_lost_degree
#print axioms branches_of_complete_limit
#print axioms period_of_stable_limit
end OrderedPartitions.RootTracking
