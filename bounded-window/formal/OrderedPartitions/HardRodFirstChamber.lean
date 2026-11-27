import OrderedPartitions.HardRodAffineReadout
import OrderedPartitions.HardRodStableDegree
import OrderedPartitions.AffineRoots

noncomputable section
namespace OrderedPartitions.RootTracking
open Filter Polynomial InterlacingStep Kernel
open scoped Topology

/-- Both true rows are linear before the first degree increase. -/
theorem original_linear_pair {j n : ℕ} (hj : 2≤j) (lo : j≤n) (hi : n+1<2*j) :
    OrderedPair 1 (row n j) (row (n+1) j) := by
  obtain ⟨l,r,lr,neg,hl,hr⟩ := original_affine_roots hj lo hi
  have array {k : ℕ} {u : ℝ} (start : j≤k) (stop : k<2*j) (uneg : u<0)
      (root : (row k j).IsRoot u) : RootArray (row k j) (fun _ : Fin 1 ↦ u) := by
    have cap : k<(1+1)*j := stop
    have deg := (original_window_degree (M:=1) hj cap).trans
      (window_shape (M:=1) (D:=1) hj (by decide) (by decide) (by simpa using start) cap).1
    exact ⟨fun a b hab ↦ by have := a.isLt;have := b.isLt;omega,fun _ ↦ uneg,
      fun hz ↦ by simp [hz] at deg,deg,fun _ ↦ root⟩
  exact ⟨_,array lo (by omega) (lr.trans neg) ((hl l).2 rfl),Or.inl
    ⟨_,array (by omega) hi neg ((hr r).2 rfl),fun _ ↦ lr,
      fun a b hab ↦ by have := a.isLt;have := b.isLt;omega⟩⟩

theorem original_at_ratio_one {J N : ℕ→ℕ} (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 1))
    (lo : ∀ i,J i≤N i) :
    ∀ᶠ i in atTop, OrderedPair 1 (row (N i) (J i)) (row (N i+1) (J i)) := by
  filter_upwards [hj.eventually_ge_atTop 3,hn.eventually_lt_const (show (1:ℝ)<3/2 by norm_num)]
    with i high frac
  have jp : (0:ℝ)<J i := by exact_mod_cast (show 0<J i by omega)
  have J3 : (3:ℝ)≤J i := by exact_mod_cast high
  have bound := (div_lt_iff₀ jp).mp frac
  have hnext : (N i:ℝ)+1<2*(J i:ℝ) := by linarith
  exact original_linear_pair (by omega) (lo i) (by exact_mod_cast hnext)

#print axioms original_linear_pair
#print axioms original_at_ratio_one
end OrderedPartitions.RootTracking
