import OrderedPartitions.HardRodBoundary
import OrderedPartitions.HardRodPolynomial

noncomputable section
open Filter PowerSeries
open scoped Topology
namespace OrderedPartitions.Kernel

def windowSpeed (j n d : ℕ) := (j:ℝ)*(windowCoeff j (n+1) d - windowCoeff j n d)

private theorem masked_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    (p : ℕ → Prop) [DecidablePred p] :
    Tendsto (fun i ↦ if p i then f i else 0) atTop (𝓝 0) := by
  rw [tendsto_def] at hf ⊢
  intro s hs
  filter_upwards [hf s hs] with i hi
  change (if p i then f i else 0) ∈ s
  split <;> first | exact hi | exact mem_of_mem_nhds hs

private theorem clipped_value (j n d : ℕ) (hj : 1≤j) :
    windowCoeff j n d =
      windowCoeff j (n-d*j+d*j) d + (if n<d*j then -windowCoeff j (d*j) d else 0) := by
  by_cases h : n<d*j
  · rw [window_before hj h,if_pos h,Nat.sub_eq_zero_of_le h.le,zero_add,add_neg_cancel]
  · simp [h,Nat.sub_add_cancel (by omega : d*j≤n)]

private theorem clipped_speed (j n d : ℕ) (hj : 1≤j) :
    windowSpeed j n d = windowSpeed j (n-d*j+d*j) d +
      (if n<d*j then -windowSpeed j (d*j) d else 0) +
      (if n+1=d*j then (j:ℝ)*windowCoeff j (d*j) d else 0) := by
  by_cases h : n<d*j
  · rw [if_pos h,Nat.sub_eq_zero_of_le h.le,zero_add,add_neg_cancel,zero_add,windowSpeed,window_before hj h,sub_zero]
    split_ifs with eq
    · rw [eq]
    · rw [window_before hj (by omega : n+1<d*j),mul_zero]
  · simp [h,Nat.sub_add_cancel (by omega : d*j≤n),show n+1≠d*j by omega]

theorem window_higher_limits {J N : ℕ → ℕ} {x : ℝ} (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (h : ℕ) :
    let d := h+2
    Tendsto (fun i ↦ windowCoeff (J i) (N i) d) atTop (𝓝 ((max (x-d) 0)^d/(d.factorial:ℝ))) ∧
    Tendsto (fun i ↦ windowSpeed (J i) (N i) d) atTop (𝓝 ((d:ℝ)*(max (x-d) 0)^(h+1)/(d.factorial:ℝ))) := by
  let d := h+2
  let S := fun i ↦ N i-d*J i
  let y := max (x-d) 0
  have sr : Tendsto (fun i ↦ (S i:ℝ)/(J i:ℝ)) atTop (𝓝 y) := residual_ratio_limit hj hn d
  obtain ⟨vl,sl⟩ := original_window_limits hj sr (h+1) (Or.inl (by omega))
  have zr : Tendsto (fun i ↦ ((fun _ : ℕ ↦ 0 : ℕ → ℕ) i:ℝ)/(J i:ℝ)) atTop (𝓝 0) := by simp
  obtain ⟨ev,es⟩ := original_window_limits hj zr (h+1) (Or.inl (by omega))
  have ev' : Tendsto (fun i ↦ windowCoeff (J i) (d*J i) d) atTop (𝓝 0) := by simpa [d] using ev
  have es' : Tendsto (fun i ↦ windowSpeed (J i) (d*J i) d) atTop (𝓝 0) := by simpa [d,windowSpeed] using es
  let p := fun i ↦ N i<d*J i
  let q := fun i ↦ N i+1=d*J i
  have zv := masked_zero (show Tendsto _ _ (𝓝 0) from by simpa using ev'.neg) p
  have zs := masked_zero (show Tendsto _ _ (𝓝 0) from by simpa using es'.neg) p
  have entry := masked_zero (entry_speed_limit hj h) q
  constructor
  · apply (show Tendsto _ _ (𝓝 (y^d/(d.factorial:ℝ))) from by simpa only [add_zero] using vl.add zv).congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i hi
    exact (clipped_value (J i) (N i) d hi).symm
  · have cv : ((h+1:ℕ):ℝ)+1=(d:ℝ) := by dsimp [d]; push_cast;ring
    rw [cv] at sl
    have t := (sl.add zs).add entry
    apply (show Tendsto _ _ (𝓝 ((d:ℝ)*y^(h+1)/(d.factorial:ℝ))) from by simpa only [add_zero] using t).congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i hi
    exact (clipped_speed (J i) (N i) d hi).symm

private theorem first_degree_limits {J N : ℕ → ℕ} {x : ℝ} (hx : 1<x) (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) :
    Tendsto (fun i ↦ windowCoeff (J i) (N i) 1) atTop (𝓝 (x-1)) ∧
    Tendsto (fun i ↦ windowSpeed (J i) (N i) 1) atTop (𝓝 1) := by
  let S := fun i ↦ N i-J i
  have rs : Tendsto (fun i ↦ (S i:ℝ)/(J i:ℝ)) atTop (𝓝 (x-1)) := by
    simpa [S,max_eq_left (sub_nonneg.mpr hx.le)] using residual_ratio_limit hj hn 1
  have inf : Tendsto S atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R:=ℝ)).mp
    apply ((tendsto_natCast_atTop_atTop.comp hj).atTop_mul_pos (sub_pos.mpr hx) rs).congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i ji
    have nz : (J i:ℝ)≠0 := by exact_mod_cast (show J i≠0 by omega)
    change (J i:ℝ)*((S i:ℝ)/(J i:ℝ))=S i
    field_simp
  obtain ⟨vl,sl⟩ := original_window_limits hj rs 0 (Or.inr inf)
  have ac : ∀ᶠ i in atTop, S i+J i=N i := by
    filter_upwards [hj.eventually_ge_atTop 1,hn.eventually (lt_mem_nhds hx)] with i ji ni
    have jp : 0<(J i:ℝ) := by exact_mod_cast (show 0<J i by omega)
    have r := (lt_div_iff₀ jp).mp ni
    exact Nat.sub_add_cancel (by exact_mod_cast (show (J i:ℝ)≤N i by linarith))
  constructor
  · apply (show Tendsto _ _ (𝓝 (x-1)) from by simpa using vl).congr'
    filter_upwards [ac] with i hi
    simp [hi]
  · apply (show Tendsto _ _ (𝓝 (1:ℝ)) from by simpa using sl).congr'
    filter_upwards [ac] with i hi
    simp [windowSpeed,hi]

theorem window_coeff_limit {J N : ℕ → ℕ} {x : ℝ} (hx : 1<x) (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (d : ℕ) :
    Tendsto (fun i ↦ windowCoeff (J i) (N i) d) atTop (𝓝 (HardRod.rodCoeff d x)) := by
  match d with
  | 0 =>
    rw [HardRod.rodCoeff_zero]
    apply (tendsto_const_nhds (x:=(1:ℝ))).congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i ji
    simp [windowCoeff,normalizedMoment,markedCount_zero,(original_eval_pos ji _).ne']
  | 1 => simpa [HardRod.rodCoeff,max_eq_left (sub_nonneg.mpr hx.le)] using (first_degree_limits hx hj hn).1
  | h+2 => exact (window_higher_limits hj hn h).1

theorem window_speed_limit {J N : ℕ → ℕ} {x : ℝ} (hx : 1<x) (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x)) (h : ℕ) :
    Tendsto (fun i ↦ windowSpeed (J i) (N i) (h+1)) atTop (𝓝 (HardRod.rodCoeff h (x-1))) := by
  cases h with
  | zero => simpa using (first_degree_limits hx hj hn).2
  | succ h =>
    have w := (window_higher_limits hj hn h).2
    convert w using 2
    unfold HardRod.rodCoeff
    rw [Nat.factorial_succ (h+1),Nat.cast_mul,Nat.cast_succ,Nat.cast_succ]
    have hz : (h:ℝ)+1+1≠0 := by positivity
    have e : x-1-((h:ℝ)+1)=x-((h:ℝ)+1+1) := by ring
    rw [e]
    push_cast
    field_simp

#print axioms window_coeff_limit
#print axioms window_speed_limit
#print axioms window_higher_limits
end OrderedPartitions.Kernel
