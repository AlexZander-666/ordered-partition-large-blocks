import OrderedPartitions.HardRodRightBrackets
import OrderedPartitions.HardRodWindowPoly

noncomputable section
namespace OrderedPartitions.RootTracking
open Filter Polynomial InterlacingStep Kernel HardRod
open scoped Topology

/-- The finite branches exist simultaneously, without a hypothesis on the degrees
of the old or new finite rows. The upper signs are evaluated at actual lower zeros. -/
theorem finite_branches {J N : ℕ→ℕ} {x : ℝ} {d M : ℕ}
    (cap : d≤M) (lo : (d:ℝ)+1<x) (hi : x≤(d:ℝ)+2)
    (hj : Tendsto J atTop atTop) (hn : Tendsto (fun n ↦ (N n:ℝ)/(J n:ℝ)) atTop (𝓝 x)) :
    ∃ b : Fin (d+1)→ℝ, ∃ z : ℕ→Fin (d+1)→ℝ, RootArray (phi (M+1) x) b ∧
      (∀ i,Tendsto (fun n ↦ z n i) atTop (𝓝 (b i))) ∧
      ∀ᶠ n in atTop, StrictMono (z n) ∧ ∀i,z n i<0 ∧
        (windowPoly (M+1) (J n) (N n)).eval (z n i)=0 ∧
        0<(-1:ℝ)^(d+1-i.val)*(windowPoly (M+1) (J n) (N n+1)).eval (z n i) := by
  have dN : d+1≤M+1 := by omega
  have hx : 1<x := by linarith [Nat.cast_nonneg (α:=ℝ) d]
  obtain ⟨a,b,ha,hb,ord⟩ := unit_interlacing d dN lo hi
  have rowConv (t : ℝ) := (original_moving_limits hx hj hn (Y:=fun _ ↦ t) tendsto_const_nhds M).1
  have each (i : Fin (d+1)) := simple_branch rowConv (hb.zeros i) (fun zero ↦ by
    have res := phi_residue d dN lo hi (hb.zeros i)
    simp [zero] at res)
  choose z lim roots using each
  refine ⟨b,fun n i ↦ z i n,hb,lim,?_⟩
  have sorted : ∀ᶠ n in atTop, StrictMono (fun i ↦ z i n) := by
    have pair (i j : Fin (d+1)) : ∀ᶠ n in atTop, i<j → z i n<z j n := by
      by_cases h : i<j
      · exact ((lim i).eventually_lt (lim j) (hb.ordered h)).mono (fun _ lt _ ↦ lt)
      · exact .of_forall fun _ lt ↦ (h lt).elim
    filter_upwards [eventually_all.mpr fun i ↦ eventually_all.mpr (pair i)] with n hs
    exact fun i j ij ↦ hs i j ij
  apply sorted.and
  apply eventually_all.mpr
  intro i
  have low := phi_shape (N:=M+1) (d:=d) (x:=x-1) (by omega) (by linarith) (by linarith)
  have sep := eval_between_sign ha hb.ordered ord low.2.1 i
  have same : phi M (x-1)=phi (M+1) (x-1) := by
    have cm : (d:ℝ)≤M := by exact_mod_cast cap
    apply phi_stable <;> push_cast <;> linarith
  have sgn : 0 < (-1:ℝ)^(d+1-i.val)*(b i * (phi M (x-1)).eval (b i)) := by
    rw [same,show d+1-i.val=d-i.val+1 by omega,pow_succ]
    calc 0 < (-(b i))*((-1:ℝ)^(d-i.val)*(phi (M+1) (x-1)).eval (b i)) :=
            mul_pos (neg_pos.mpr (hb.negative i)) sep
         _ = _ := by ring
  have v := (original_moving_limits hx hj hn (lim i) M).2.const_mul ((-1:ℝ)^(d+1-i.val))
  filter_upwards [(lim i).eventually_lt_const (hb.negative i),roots i,v.eventually_const_lt sgn,
    hj.eventually_ge_atTop 1] with n neg old sign jpos
  refine ⟨neg,old,?_⟩
  change 0 < _ * (speedPoly _ _ _).eval _ at sign
  simp only [speedPoly,eval_mul,eval_C,eval_sub,old,sub_zero] at sign
  rw [mul_left_comm] at sign
  exact pos_of_mul_pos_right sign (Nat.cast_nonneg _)

#print axioms finite_branches
end OrderedPartitions.RootTracking
