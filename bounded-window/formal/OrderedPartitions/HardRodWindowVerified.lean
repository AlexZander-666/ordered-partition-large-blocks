import OrderedPartitions.HardRodFullPeriodRows

noncomputable section
namespace OrderedPartitions
open Filter Polynomial Kernel RootTracking
open scoped Topology

private theorem chamber_degree {n j D : ℕ} (jp : 0<j) (lo : D*j≤n) (hi : n<(D+1)*j) :
    n/j=D := by
  exact le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul jp).mpr hi))
    ((Nat.le_div_iff_mul_le jp).mpr lo)

/-- For any fixed upper ratio C, the old row and its full-period successor
strictly interlace in all ranks once the threshold is sufficiently large. -/
theorem original_full_period_bounded_ratio (C : ℝ) :
    ∃ K : ℕ, ∀ j≥K, ∀ n : ℕ, j≤n → (n:ℝ)≤C*(j:ℝ) →
      OrderedPair (n/j) (row n j) (row (n+j) j) := by
  apply uniform_ratio_of_chambers
  intro D pos
  apply uniform_chamber_of_limits
  intro J N x xlo xhi hj hn rk
  have eqd : ∀ᶠ i in atTop,N i/J i=D := by
    filter_upwards [hj.eventually_ge_atTop 1] with i ji
    exact chamber_degree (by omega) (rk i).1 (rk i).2
  rcases eq_or_lt_of_le xlo with rfl|gt
  · obtain ⟨r,rfl⟩ : ∃r,D=r+1 := ⟨D-1,by omega⟩
    let M := fun i ↦ N i-(r+1)*J i
    have recover (i) : M i+(r+1)*J i=N i := Nat.sub_add_cancel (rk i).1
    have shift (i) : M i+(r+2)*J i=N i+J i := by
      rw [show r+2=r+1+1 by omega,Nat.add_mul,one_mul,←Nat.add_assoc,recover]
    have hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0) := by
      apply (show Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)-((r+1:ℕ):ℝ)) atTop (𝓝 0) by
        simpa using hn.sub_const ((r+1:ℕ):ℝ)).congr'
      filter_upwards [hj.eventually_ge_atTop 1] with i ji
      have w : (J i:ℝ)≠0 := by exact_mod_cast (show J i≠0 by omega)
      rw [show (M i:ℝ)=(N i:ℝ)-((r+1:ℕ):ℝ)*(J i:ℝ) by
        simp [M,Nat.cast_sub (rk i).1]]
      field_simp
    filter_upwards [actual_period_integer r hj hm,eqd] with i ok deg
    simpa only [recover,shift,deg] using ok
  · filter_upwards [actual_period_stable pos gt xhi hj hn rk,eqd] with i ok deg
    simpa only [deg] using ok

private theorem original_degree_on_chamber {n j : ℕ} (jj : 2≤j) (nj : j≤n) :
    (row n j).natDegree=n/j := by
  have jp : 0<j := by omega
  have cap := (Nat.div_lt_iff_lt_mul jp).mp (Nat.lt_succ_self (n/j))
  rw [original_window_degree jj cap]
  exact (window_shape jj ((Nat.le_div_iff_mul_le jp).mpr (by simpa using nj))
    (le_refl _) (Nat.div_mul_le_self _ _) cap).1

/-- The complete original rows strictly interlace for every shift from 1
through the threshold simultaneously. The threshold bound may depend on C. -/
theorem original_full_window_bounded_ratio (C : ℝ) :
    ∃ K : ℕ, ∀ j≥K, ∀ n : ℕ, j≤n → (n:ℝ)≤C*(j:ℝ) →
      ∀ h, 1≤h → h≤j → OrderedPair (n/j) (row n j) (row (n+h) j) := by
  obtain ⟨K₁,one⟩ := original_interlacing_bounded_ratio (C+1)
  obtain ⟨K₂,full⟩ := original_full_period_bounded_ratio C
  refine ⟨max 2 (max K₁ K₂),?_⟩
  intro j jj n nj cap h hh hj
  have j2 : 2≤j := (le_max_left _ _).trans jj
  have a : K₁≤j := (le_max_left _ _).trans ((le_max_right _ _).trans jj)
  have b : K₂≤j := (le_max_right _ _).trans ((le_max_right _ _).trans jj)
  let P := fun u ↦ row (n+u) j
  have deg (u : ℕ) : (P u).natDegree=(n+u)/j :=
    original_degree_on_chamber j2 (nj.trans (Nat.le_add_right _ _))
  have steps (u : ℕ) (small : u<j) : OrderedPair (P u).natDegree (P u) (P (u+1)) := by
    rw [deg]
    have ub : ((n+u:ℕ):ℝ)≤(C+1)*(j:ℝ) := by
      push_cast; linarith [show (u:ℝ)≤j by exact_mod_cast small.le]
    simpa only [P,Nat.add_assoc] using one j a (n+u) (by omega) ub
  have ord : Monotone fun u ↦ (P u).natDegree := by
    intro v w vw
    change (P v).natDegree ≤ (P w).natDegree
    rw [deg,deg]
    exact Nat.div_le_div_right (Nat.add_le_add_left vw _)
  have width : (P j).natDegree≤(P 0).natDegree+1 := by
    simp only [deg,Nat.add_zero,Nat.add_div_right _ (by omega : 0<j),le_refl]
  have per : OrderedPair (P 0).natDegree (P 0) (P j) := by
    simpa only [P,Nat.add_zero,original_degree_on_chamber j2 nj] using full j b n nj cap
  simpa only [P,Nat.add_zero,original_degree_on_chamber j2 nj] using
    orderedPair_window_of_period ord steps width per hh hj

#print axioms original_full_period_bounded_ratio
#print axioms original_full_window_bounded_ratio
end OrderedPartitions
