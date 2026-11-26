import OrderedPartitions.CubicThirdEnvelope

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

private theorem sharpW (s : ℕ) : (s:ℝ)^2/2+2.52*s+2≤w s ∧ w s≤(s:ℝ)^2/2+2.55*s+2.86 := by
  have ⟨l,h⟩ := abs_le.mp ((w_error s).trans (div_le_self (by norm_num) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))))
  unfold wMain at l h
  have rs := rho_interval
  have a := mul_le_mul_of_nonneg_right rs.1.le (Nat.cast_nonneg (α:=ℝ) s)
  have b := mul_le_mul_of_nonneg_right rs.2.le (Nat.cast_nonneg (α:=ℝ) s)
  have c := pow_le_pow_left₀ (by norm_num) rs.1.le 2
  have d := pow_le_pow_left₀ (show 0≤rho by linarith [rs.1]) rs.2.le 2
  constructor <;> nlinarith only [l,h,rs.1,rs.2,a,b,c,d,Nat.cast_nonneg (α:=ℝ) s]

private theorem wCap {s i : ℕ} (hi : i≤s) : w i≤(s:ℝ)^2/2+2.55*s+2.86 := by
  apply (sharpW i).2.trans
  have le : (i:ℝ)≤s := by exact_mod_cast hi
  gcongr

private theorem wPos (i : ℕ) : 0≤w i := (by positivity : (0:ℝ)≤(i+1:ℝ)*(i+2)/2).trans (w_bounds i).1

theorem quadratic_raw_envelope {j s : ℕ} (hj : 64≤j) (hs : j≤s) :
    (s:ℝ)^2/2+2.52*s+2+cBeta j*s^2≤quadraticRaw j s ∧
      quadraticRaw j s≤cMass j^2*((s:ℝ)^2/2+2.55*s+2.86) := by
  cases s with
  | zero => omega
  | succ u =>
    rw [cQuadratic_conv]
    have z := (conv_two (h:=2) (s:=u) hj w (fun i _ ↦ wPos i)
      (fun i hi ↦ wCap (s:=u+1) (by omega : i≤u+1)) (by positivity)).1
    have up := (conv_majorant (h:=2) hj (u+1) w (fun i _ ↦ wPos i) (fun _ ↦ wCap) (by positivity)).2
    rw [cWeight_one] at z
    have old := (sharpW (u+1)).1
    have old1 : ((u:ℝ)+1)^2/2≤w u := by nlinarith only [(w_bounds u).1,Nat.cast_nonneg (α:=ℝ) u]
    have wb := mul_le_mul (beta_weight hj).1 old1 (by positivity) (marker_positive j 1).le
    push_cast at *
    exact ⟨by nlinarith only [z,old,wb],up⟩

private theorem dwCap {s i : ℕ} (hi : i≤s+1) : 0≤deltaSeq w i ∧ deltaSeq w i≤(s:ℝ)+3.54 := by
  cases i with
  | zero =>
    have k0 : constantCoeff K=2*rho := by
      rw [← coeff_zero_eq_constantCoeff_apply,k_row (j:=1) (by decide),row_zero (by decide)]
      simp
    rw [deltaSeq,show w 0=(2*rho)^3 by simp [w,coeff_zero_eq_constantCoeff_apply,k0]]
    have r : 0≤2*rho := by linarith [rho_interval.1]
    exact ⟨by positivity,by linarith [pow_le_pow_left₀ r (show 2*rho≤1.4 by linarith [rho_interval.2]) 3,Nat.cast_nonneg (α:=ℝ) s]⟩
  | succ i =>
    change 0≤w (i+1)-w i ∧ _≤_
    have e := (abs_le.mp ((w_increment_error i).trans (div_le_self (by norm_num) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))))).2
    have le : (i:ℝ)≤s := by exact_mod_cast (by omega : i≤s)
    exact ⟨by linarith [(w_increment i).1,Nat.cast_nonneg (α:=ℝ) i],by dsimp [deltaSeq]; linarith [rho_interval.2]⟩

theorem quadratic_step_envelope {j s : ℕ} (hj : 64≤j) (hs : j≤s) :
    (s:ℝ)+3+2*cBeta j*s ≤ quadraticRaw j (s+1)-quadraticRaw j s ∧
    quadraticRaw j (s+1)-quadraticRaw j s≤cMass j^2*((s:ℝ)+3.54) := by
  cases s with
  | zero => omega
  | succ u =>
    rw [cQuadratic_conv,cQuadratic_conv,conv_delta]
    have z := (conv_two (h:=2) (s:=u+1) hj (deltaSeq w)
      (fun _ hi ↦ (dwCap hi).1) (fun i hi ↦ (dwCap (s:=u+1) (by omega : i≤u+1+1)).2) (by positivity)).1
    have up := (conv_majorant (h:=2) hj (u+1+1) (deltaSeq w)
      (fun _ hi ↦ (dwCap hi).1) (fun _ hi ↦ (dwCap hi).2) (by positivity)).2
    rw [cWeight_one] at z
    simp only [deltaSeq] at z
    have pot : (2:ℝ)^5≤2^(u+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have cap : (48/100:ℝ)/2^(u+1)≤0.02 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have e := (abs_le.mp ((w_increment_error (u+1)).trans cap)).1
    have old1 : (u:ℝ)+1≤w (u+1)-w u := by linarith [(w_increment u).1]
    have wb := mul_le_mul (beta_weight hj).1 old1 (by positivity) (marker_positive j 1).le
    push_cast at *
    exact ⟨by nlinarith only [z,e,wb,rho_interval.1],up⟩

#print axioms quadratic_raw_envelope
#print axioms quadratic_step_envelope
end OrderedPartitions.Kernel
