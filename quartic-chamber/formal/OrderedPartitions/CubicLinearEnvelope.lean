import OrderedPartitions.CubicThirdEnvelope

noncomputable section
open PowerSeries Finset
namespace OrderedPartitions.Kernel

private theorem bigpow {s : ℕ} (hs : 63≤s) : 105*((s:ℝ)+1)≤ (4:ℝ)^s := by
  induction s,hs using Nat.le_induction with
  | base => norm_num
  | succ s h ih => rw [pow_succ]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) s]

private theorem damped_step {j s : ℕ} (hj : 64≤j) (js : j≤s+1) :
    |g (s+1)-g s-1|≤cEta j/2 := by
  have p := bigpow (s:=s) (by omega)
  have le : (j:ℝ)≤s+1 := by exact_mod_cast js
  apply (g_increment_error s).trans
  have jp : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  unfold cEta cq
  field_simp
  nlinarith only [p,le]

private theorem cgDelta (s : ℕ) : 0≤deltaSeq g s ∧ deltaSeq g s≤2 := by
  cases s with
  | zero =>
    have k0 : constantCoeff K=2*rho := by
      rw [← coeff_zero_eq_constantCoeff_apply,k_row (j:=1) (by decide),row_zero (by decide)]
      simp
    rw [deltaSeq,show g 0=(2*rho)^2 by simp [g,coeff_zero_eq_constantCoeff_apply,k0]]
    exact ⟨sq_nonneg _,(pow_le_pow_left₀ (show 0≤2*rho by linarith [rho_interval.1])
      (show 2*rho≤1.4 by linarith [rho_interval.2]) 2).trans (by norm_num)⟩
  | succ s => exact ⟨(g_increment s).1.le,(g_increment s).2.le⟩

private theorem sharpG {s : ℕ} (hs : 4≤s) : (s:ℝ)+1.68≤g s ∧ g s≤(s:ℝ)+1.72 := by
  have large : (4:ℝ)^4≤4^s := pow_le_pow_right₀ (by norm_num) hs
  have h := abs_le.mp ((g_error s).trans (show (42/100:ℝ)/4^s ≤0.01 from
    (div_le_iff₀ (by positivity)).mpr (by linarith)))
  unfold gMain at h
  constructor <;> linarith [h.1,h.2,rho_interval.1,rho_interval.2]

theorem linear_raw_envelope {j s : ℕ} (hj : 64≤j) (hs : j≤s) :
    (s:ℝ)+1.68+cBeta j*s≤linearRaw j s ∧ linearRaw j s≤cMass j*((s:ℝ)+1.72) := by
  cases s with
  | zero => omega
  | succ u =>
    rw [cLinear_conv]
    have pos (i : ℕ) : 0≤g i := by linarith [(g_bounds i).1,Nat.cast_nonneg (α:=ℝ) i]
    have cap (i : ℕ) (hi : i≤u+1) : g i≤(↑(u+1):ℝ)+1.72 := by
      by_cases ei : i=u+1
      · subst i; exact (sharpG (s:=u+1) (by omega)).2
      · have iR : (i:ℝ)+1≤u+1 := by exact_mod_cast (show i+1≤u+1 by omega)
        have h := abs_le.mp ((g_error i).trans (div_le_self (by norm_num) (one_le_pow₀ (by norm_num : (1:ℝ)≤4))))
        unfold gMain at h
        push_cast; linarith [h.2,rho_interval.2]
    have both := conv_majorant (h:=1) hj (u+1) g (fun i _ ↦ pos i) cap (by positivity)
    have two := (conv_two (h:=1) (s:=u) hj g (fun i _ ↦ pos i) (fun i hi ↦ cap i (by omega)) (by positivity)).1
    simp only [cWeight_one,Nat.cast_one,one_mul] at two
    have prod := mul_le_mul (beta_weight hj).1 (g_bounds u).1 (by positivity) (marker_positive j 1).le
    have lower := (sharpG (s:=u+1) (by omega)).1
    push_cast at *
    exact ⟨by linarith only [two,lower,prod],by simpa using both.2⟩

theorem linear_step_envelope {j s : ℕ} (hj : 64≤j) (hs : j≤s) :
    1+cBeta j-cEta j ≤ linearRaw j (s+1)-linearRaw j s ∧
    linearRaw j (s+1)-linearRaw j s ≤ 1+2*(cMass j-1)-cBeta j+cEta j := by
  cases s with
  | zero => omega
  | succ u =>
    rw [cLinear_conv,cLinear_conv,conv_delta]
    have two := conv_two (h:=1) (s:=u+1) hj (deltaSeq g) (fun i _ ↦ (cgDelta i).1)
      (fun i _ ↦ (cgDelta i).2) (by norm_num)
    simp only [cWeight_one,Nat.cast_one,one_mul,pow_one,deltaSeq] at two
    have a := abs_le.mp (damped_step (s:=u) hj hs)
    have b := abs_le.mp (damped_step (s:=u+1) hj (by omega))
    have wt := beta_weight hj
    have non := (marker_positive j 1).le
    have prod := abs_le.mp (show |coeff 1 (markerB j)*(g (u+1)-g u-1)|≤cEta j/2 from by
      rw [abs_mul,abs_of_nonneg non]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr a) non).trans (by
        simpa using mul_le_mul_of_nonneg_right wt.2 (show 0≤cEta j/2 by unfold cEta; positivity [cq_pos hj])))
    constructor <;> nlinarith only [two.1,two.2,a.1,a.2,b.1,b.2,prod.1,prod.2,wt.1]

#print axioms linear_raw_envelope
#print axioms linear_step_envelope
end OrderedPartitions.Kernel
