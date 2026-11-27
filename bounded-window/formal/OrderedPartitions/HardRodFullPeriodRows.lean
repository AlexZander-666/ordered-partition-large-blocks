import OrderedPartitions.HardRodFullPeriodBranches
import OrderedPartitions.HardRodFullPeriodLimits
import OrderedPartitions.HardRodBoundedRatio

noncomputable section
namespace OrderedPartitions.RootTracking
open Filter Polynomial InterlacingStep Kernel HardRod
open scoped Topology

private theorem ratio_next {J N : ℕ→ℕ} {x : ℝ} (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) :
    Tendsto (fun i ↦ ((N i + J i:ℕ):ℝ)/(J i:ℝ)) atTop (𝓝 (x+1)) := by
  apply (hn.add_const 1).congr'
  filter_upwards [hj.eventually_ge_atTop 1] with i ji
  rw [Nat.cast_add,add_div,div_self (by exact_mod_cast (show J i≠0 by omega))]

private theorem original_period_transfer {d M K j n n' : ℕ} (hj : 2≤j)
    (pa : n<(M+1)*j) (qa : n'<(K+1)*j)
    (pair : OrderedPair d (windowPoly M j n) (windowPoly K j n')) :
    OrderedPair d (row n j) (row n' j) := by
  obtain ⟨u,p,same|more⟩ := pair
  · obtain ⟨v,q,h⟩ := same
    exact ⟨_,original_root_array hj pa p,Or.inl ⟨_,original_root_array hj qa q,
      fun i ↦ originalCoordinate_mono hj (h.1 i),fun i l il ↦ originalCoordinate_mono hj (h.2 i l il)⟩⟩
  · obtain ⟨v,q,h⟩ := more
    exact ⟨_,original_root_array hj pa p,Or.inr ⟨_,original_root_array hj qa q,
      fun i ↦ ⟨originalCoordinate_mono hj (h i).1,originalCoordinate_mono hj (h i).2⟩⟩⟩

/-- All real ranks at a full-period jump if the limiting chamber is entered
strictly above its left endpoint. Its right endpoint is allowed. -/
theorem actual_period_stable {J N : ℕ→ℕ} {D : ℕ} {x : ℝ} (pos : 1≤D)
    (lo : (D:ℝ)<x) (hi : x≤(D:ℝ)+1) (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x))
    (rank : ∀ i, D*J i≤N i ∧ N i<(D+1)*J i) :
    ∀ᶠ i in atTop, OrderedPair D (row (N i) (J i)) (row (N i+J i) (J i)) := by
  have upper := ratio_next hj hn
  have x1 : 1<x := by exact lt_of_le_of_lt (by exact_mod_cast pos) lo
  obtain ⟨u,v,hu,hv,sep⟩ := unit_interlacing D (N:=D+1) (le_refl _) (x:=x+1) (by linarith) (by linarith)
  rw [add_sub_cancel_right] at hu
  let P := fun i ↦ windowPoly (D+1) (J i) (N i)
  let Q := fun i ↦ windowPoly (D+1) (J i) (N i+J i)
  have pp (t : ℝ) := (original_moving_limits x1 hj hn (Y:=fun _ ↦ t) tendsto_const_nhds D).1
  have qq (t : ℝ) := (original_moving_limits (by linarith : 1<x+1) hj upper
    (Y:=fun _ ↦ t) tendsto_const_nhds D).1
  have bounds (i : ℕ) : (D+1)*J i ≤ N i+J i ∧ N i+J i < (D+1+1)*J i := by
    obtain ⟨a,b⟩ := rank i
    simpa only [Nat.add_mul,one_mul] using And.intro (Nat.add_le_add_right a (J i))
      (Nat.add_lt_add_right b (J i))
  have sh : ∀ᶠ i in atTop, P i≠0 ∧ (P i).natDegree=D ∧ Q i≠0 ∧ (Q i).natDegree=D+1 := by
    filter_upwards [hj.eventually_ge_atTop 2] with i j2
    have a := window_shape (M:=D+1) j2 pos (Nat.le_succ _) (rank i).1 (rank i).2
    have b := window_shape (M:=D+1) j2 (Nat.succ_pos D) (le_refl _) (bounds i).1 (bounds i).2
    exact ⟨Polynomial.leadingCoeff_ne_zero.mp a.2.1.ne',a.1,Polynomial.leadingCoeff_ne_zero.mp b.2.1.ne',b.1⟩
  have result := period_of_stable_limit hu hv sep pp qq sh
  filter_upwards [result,hj.eventually_ge_atTop 2] with i h ji
  exact original_period_transfer ji ((rank i).2.trans_le (Nat.mul_le_mul_right _ (by omega))) (bounds i).2 h

private theorem offset_ratio {J M : ℕ → ℕ} (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) (d : ℕ) :
    Tendsto (fun i ↦ ((M i+d*J i:ℕ):ℝ)/(J i:ℝ)) atTop (𝓝 (d:ℝ)) := by
  apply (show Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)+(d:ℝ)) atTop (𝓝 (d:ℝ)) by
    simpa using hm.add_const (d:ℝ)).congr'
  filter_upwards [hj.eventually_ge_atTop 1] with i ji
  push_cast
  have nz : (J i:ℝ)≠0 := by exact_mod_cast (show J i≠0 by omega)
  field_simp

private theorem one_shape {j m : ℕ} (hj : 1≤j) (t : ℝ) :
    (windowPoly 1 j (m+j)).eval t = 1+windowCoeff j (m+j) 1*t := by
  simp [windowPoly_eval,Finset.sum_range_succ,windowCoeff,normalizedMoment,markedCount_zero,
    (original_eval_pos hj _).ne']

private theorem first_top_vanish {J M : ℕ → ℕ} (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ windowCoeff (J i) (M i+J i) 1) atTop (𝓝 0) := by
  have hi : Tendsto (fun i ↦ 18*((M i:ℝ)+1)/(J i:ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero,div_eq_mul_inv,add_mul,one_mul,mul_assoc] using
      (hm.add (cutoff_inv_limit hj)).const_mul (18:ℝ)
  apply squeeze_zero' _ _ hi
  · filter_upwards [hj.eventually_ge_atTop 2] with i ji
    simpa using (windowCoeff_positive ji (le_refl 1) (M i)).le
  · filter_upwards [hj.eventually_ge_atTop 50] with i ji
    have nz := (original_eval_pos (by omega : 1≤J i) (M i)).ne'
    have b := full_period_leading_bound ji 0 (M i)
    have w : windowCoeff (J i) (M i) 0=1 := by
      simp [windowCoeff,normalizedMoment,markedCount_zero,nz]
    have ji' : 0<(J i:ℝ) := by exact_mod_cast (by omega : 0<J i)
    exact (le_div_iff₀ ji').mpr (by simpa [w,mul_comm (J i:ℝ)] using b)

private theorem offset_pointwise {J M : ℕ → ℕ} (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) (d : ℕ) (t : ℝ) :
    Tendsto (fun i ↦ (windowPoly (d+1) (J i) (M i+(d+1)*J i)).eval t) atTop
      (𝓝 ((phi (d+1) (d+1:ℕ)).eval t)) := by
  cases d with
  | zero =>
    rw [history_eval (by norm_num)]
    apply (show Tendsto (fun i ↦ 1+windowCoeff (J i) (M i+J i) 1*t) atTop (𝓝 1) by
      simpa using ((first_top_vanish hj hm).mul_const t).const_add 1).congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i ji
    simpa using (one_shape (m:=M i) ji t).symm
  | succ r =>
    exact (original_moving_limits (by exact_mod_cast (show 1<r+1+1 by omega)) hj
      (offset_ratio hj hm _) (Y:=fun _ ↦ t) tendsto_const_nhds (r+1)).1

private theorem offset_escape {J M : ℕ → ℕ} (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) (d : ℕ) (T : ℝ) :
    ∀ᶠ i in atTop, ∃ r<T, (windowPoly (d+1) (J i) (M i+(d+1)*J i)).eval r=0 := by
  cases d with
  | zero =>
    have pos := (offset_pointwise hj hm 0 T).eventually_const_lt
      (show 0<(phi (0+1) ((0+1:ℕ):ℝ)).eval T by rw [history_eval (by norm_num)]; norm_num)
    filter_upwards [hj.eventually_ge_atTop 2,pos] with i ji p
    simp only [Nat.zero_add,Nat.one_mul] at p ⊢
    let A := windowCoeff (J i) (M i+J i) 1
    have ha : 0<A := by simpa [A] using windowCoeff_positive ji (le_refl 1) (M i)
    have h1 : 1≤J i := by omega
    rw [one_shape h1 T] at p
    have z : 1+A*T>0 := p
    refine ⟨-1/A,(div_lt_iff₀ ha).mpr (by linarith [mul_comm A T]),?_⟩
    rw [one_shape h1]
    change 1+A*(-1/A)=0
    field_simp [ha.ne']
    norm_num
  | succ r =>
    have h := windowPoly_integer_escape (d:=r+2) (by omega) hj (offset_ratio hj hm _)
      (Eventually.of_forall fun i ↦ Nat.le_add_left _ (M i)) T
    filter_upwards [h] with i e
    obtain ⟨x,xt,xz,_⟩ := e
    exact ⟨x,xt,xz⟩

/-- Every integral endpoint, including the first chamber with constant limiting
old row. The old and new rows each acquire one unbounded negative root. -/
theorem actual_period_integer {J M : ℕ→ℕ} (r : ℕ) (hj : Tendsto J atTop atTop)
    (hm : Tendsto (fun i ↦ (M i:ℝ)/(J i:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ i in atTop, OrderedPair (r+1) (row (M i+(r+1)*J i) (J i))
      (row (M i+(r+2)*J i) (J i)) := by
  have small := (offset_ratio hj hm 0).eventually_lt_const (show ((0:ℕ):ℝ)<1 by norm_num)
  have low : ∀ᶠ i in atTop, M i<J i := by
    filter_upwards [small,hj.eventually_ge_atTop 1] with i s ji
    have jp : 0<(J i:ℝ) := by exact_mod_cast (show 0<J i by omega)
    have v : (M i:ℝ)/(J i:ℝ)<1 := by simpa using s
    exact_mod_cast (show (M i:ℝ)<(J i:ℝ) by simpa using (div_lt_iff₀ jp).mp v)
  obtain ⟨u,v,p,q,sep⟩ := unit_interlacing r (N:=r+2) (by omega) (x:=((r+2:ℕ):ℝ))
    (by push_cast;linarith) (by push_cast;linarith)
  have fix : phi (r+2) (((r+2:ℕ):ℝ)-1) = phi (r+1) ((r+1:ℕ):ℝ) := by
    rw [show ((r+2:ℕ):ℝ)-1=((r+1:ℕ):ℝ) by push_cast;ring]
    apply phi_stable <;> push_cast <;> linarith
  rw [fix] at p
  let P := fun i ↦ windowPoly (r+1) (J i) (M i+(r+1)*J i)
  let Q := fun i ↦ windowPoly (r+2) (J i) (M i+(r+2)*J i)
  have bounds (i b : ℕ) (h : M i<J i) : M i+b*J i<(b+1)*J i := by
    simpa only [Nat.add_mul,one_mul,Nat.add_comm (M i)] using Nat.add_lt_add_left h (b*J i)
  have sh : ∀ᶠ i in atTop, P i≠0 ∧ (P i).natDegree=r+1 ∧ Q i≠0 ∧ (Q i).natDegree=r+2 := by
    filter_upwards [low,hj.eventually_ge_atTop 2] with i mi ji
    have a := window_shape (M:=r+1) ji (Nat.succ_pos r) (le_refl _)
      (Nat.le_add_left _ (M i)) (bounds i _ mi)
    have b := window_shape (M:=r+2) ji (Nat.succ_pos (r+1)) (le_refl _)
      (Nat.le_add_left _ (M i)) (bounds i _ mi)
    exact ⟨Polynomial.leadingCoeff_ne_zero.mp a.2.1.ne',a.1,
      Polynomial.leadingCoeff_ne_zero.mp b.2.1.ne',b.1⟩
  have pair := period_of_lost_degree p q sep (offset_pointwise hj hm r)
    (offset_pointwise hj hm (r+1)) sh
    (fun T ↦ (offset_escape hj hm r T).and (offset_escape hj hm (r+1) T))
    ((full_period_left_edge hj hm r).mono fun _ h a b ra rb ↦ h a b ra rb 0)
  filter_upwards [pair,low,hj.eventually_ge_atTop 2] with i h mi ji
  exact original_period_transfer ji (bounds i _ mi) (bounds i _ mi) h

#print axioms actual_period_integer

#print axioms actual_period_stable
end OrderedPartitions.RootTracking
