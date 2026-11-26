import OrderedPartitions.QuadraticMarker

noncomputable section
open PowerSeries Finset
namespace OrderedPartitions.Kernel

def convSeq (b f : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ i ∈ range (s+1), b i*f (s-i)

def deltaSeq (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | s+1 => f (s+1)-f s

theorem conv_delta (b f : ℕ → ℝ) (s : ℕ) :
    convSeq b f (s+1)-convSeq b f s = convSeq b (deltaSeq f) (s+1) := by
  unfold convSeq
  rw [sum_range_succ (fun i ↦ b i*f (s+1-i)), sum_range_succ (fun i ↦ b i*deltaSeq f (s+1-i))]
  simp only [Nat.sub_self,show deltaSeq f 0 = f 0 from rfl]
  have h : (∑ i ∈ range (s+1), b i*f (s+1-i))-(∑ i ∈ range (s+1), b i*f (s-i)) =
      ∑ i ∈ range (s+1), b i*deltaSeq f (s+1-i) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    rw [show s+1-i=s-i+1 by have := mem_range.mp hi; omega, deltaSeq]
    ring
  linarith

theorem conv_band (b f : ℕ → ℝ) (s : ℕ) {M U : ℝ}
    (bz : b 0=1) (bn : ∀i, 0≤b i) (mass : (∑i ∈ range (s+1), b i) ≤ M)
    (u0 : 0≤U) (bounds : ∀t≤s, 0≤f t ∧ f t≤U) :
    f s ≤ convSeq b f s ∧ convSeq b f s ≤ f s+(M-1)*U := by
  rw [sum_range_succ' b,bz] at mass
  rw [convSeq, sum_range_succ']
  simp only [bz, Nat.sub_zero, one_mul]
  have nn : 0≤∑ i ∈ range s, b (i+1)*f (s-(i+1)) :=
    sum_nonneg (fun i _ ↦ mul_nonneg (bn _) (bounds _ (Nat.sub_le ..)).1)
  have hi : (∑ i ∈ range s, b (i+1)*f (s-(i+1))) ≤
      (∑ i ∈ range s, b (i+1))*U := by
    rw [sum_mul]
    exact sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (bounds _ (Nat.sub_le ..)).2 (bn _))
  have hm := mul_le_mul_of_nonneg_right (show (∑ i ∈ range s,b (i+1)) ≤ M-1 by linarith) u0
  constructor <;> linarith

def linearRaw (j s : ℕ) : ℝ := coeff s (markerB j*K^2)
def quadraticRaw (j s : ℕ) : ℝ := coeff s (markerB j^2*K^3)

private theorem linear_conv (j s : ℕ) :
    linearRaw j s = convSeq (fun i ↦ coeff i (markerB j)) g s := by
  rw [linearRaw, coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

private theorem quad_conv (j s : ℕ) :
    quadraticRaw j s = convSeq (fun i ↦ coeff i (markerB j^2)) w s := by
  rw [quadraticRaw, coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

private theorem k0 : constantCoeff K = 2*rho := by
  rw [← coeff_zero_eq_constantCoeff_apply, k_row (j:=1) (by decide), row_zero (by decide)]
  simp

private theorem w_delta {t s : ℕ} (h : t≤s+1) :
    0 ≤ deltaSeq w t ∧ deltaSeq w t ≤ (s:ℝ)+4 := by
  cases t with
  | zero =>
    have wz : w 0 = (2*rho)^3 := by simp [w,coeff_zero_eq_constantCoeff_apply,k0]
    rw [deltaSeq,wz]
    obtain ⟨h1,h2⟩ := rho_interval
    have lo : 0≤2*rho := by linarith
    have hi : 2*rho ≤ 7/5 := by linarith
    have hc := pow_le_pow_left₀ lo hi 3
    exact ⟨by positivity, by linarith [Nat.cast_nonneg (α:=ℝ) s]⟩
  | succ t =>
    have ts : (t:ℝ)≤s := by exact_mod_cast (by omega : t≤s)
    exact ⟨by dsimp [deltaSeq]; linarith [(w_increment t).1,Nat.cast_nonneg (α:=ℝ) t],
      by dsimp [deltaSeq]; linarith [(w_increment t).2]⟩

private theorem g_delta (t : ℕ) : 0 ≤ deltaSeq g t ∧ deltaSeq g t ≤ 2 := by
  cases t with
  | zero =>
    have gz : g 0=(2*rho)^2 := by simp [g,coeff_zero_eq_constantCoeff_apply,k0]
    rw [deltaSeq,gz]
    obtain ⟨lo,hi⟩ := rho_interval
    constructor
    · positivity
    · nlinarith [mul_nonneg (show 0≤7/5-2*rho by linarith) (show 0≤7/5+2*rho by linarith)]
  | succ t => exact ⟨(g_increment t).1.le,(g_increment t).2.le⟩

private theorem sq_nonneg_coef (j i : ℕ) : 0≤coeff i (markerB j^2) := by
  rw [pow_two,coeff_mul]
  exact sum_nonneg (fun p _ ↦ mul_nonneg (marker_positive j _).le (marker_positive j _).le)

theorem raw_linear_bounds {j : ℕ} (hj : 50≤j) (s : ℕ) :
    (s:ℝ)+1 ≤ linearRaw j s ∧ linearRaw j s ≤ (1014/1000)*((s:ℝ)+3) := by
  rw [linear_conv]
  have h := conv_band _ g s (marker_zero j) (fun i ↦ (marker_positive j i).le)
    (marker_partial hj _) (show 0≤(s:ℝ)+3 by positivity) (fun t ht ↦
      ⟨by linarith [(g_bounds t).1,Nat.cast_nonneg (α:=ℝ) t],
       by linarith [(g_bounds t).2, show (t:ℝ)≤s by exact_mod_cast ht]⟩)
  exact ⟨(g_bounds s).1.trans h.1,by linarith [h.2,(g_bounds s).2]⟩

theorem raw_quadratic_bounds {j : ℕ} (hj : 50≤j) (s : ℕ) :
    (s+1:ℝ)*(s+2)/2 ≤ quadraticRaw j s ∧
      quadraticRaw j s ≤ (1029/1000)*((s:ℝ)+4)^2/2 := by
  rw [quad_conv]
  have h := conv_band _ w s (by simp [coeff_zero_eq_constantCoeff_apply,markerB,Nat.factorial_ne_zero]) (sq_nonneg_coef j)
    (marker_square_partial hj _) (show 0≤((s:ℝ)+4)^2/2 by positivity) (fun t ht ↦
      ⟨by linarith [(w_bounds t).1,show (0:ℝ)≤(t+1:ℝ)*(t+2)/2 by positivity],
       (w_bounds t).2.trans (by gcongr)⟩)
  exact ⟨(w_bounds s).1.trans h.1,by linarith [h.2,(w_bounds s).2]⟩

theorem raw_linear_increment {j s : ℕ} (hj : 50≤j) (hs : 50≤s) :
    999/1000 ≤ linearRaw j (s+1)-linearRaw j s ∧
      linearRaw j (s+1)-linearRaw j s ≤ 103/100 := by
  rw [linear_conv, linear_conv,conv_delta]
  have h := conv_band _ (deltaSeq g) (s+1) (marker_zero j) (fun i ↦ (marker_positive j i).le)
    (marker_partial hj _) (by norm_num : (0:ℝ)≤2) (fun t _ ↦ g_delta t)
  have decay := abs_le.mp (g_increment_error s)
  have pow4 : (4:ℝ)^(5:ℕ)≤4^s := pow_le_pow_right₀ (by norm_num) (by omega)
  have e := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤525/1000)
    (by norm_num : (0:ℝ)<4^5) pow4
  simp only [deltaSeq] at h
  constructor <;> linarith [h.1,h.2,decay.1,decay.2]

theorem raw_quadratic_increment {j : ℕ} (hj : 50≤j) (s : ℕ) :
    (s:ℝ)+2 ≤ quadraticRaw j (s+1)-quadraticRaw j s ∧
      quadraticRaw j (s+1)-quadraticRaw j s ≤ (1029/1000)*((s:ℝ)+4) := by
  rw [quad_conv,quad_conv,conv_delta]
  have h := conv_band _ (deltaSeq w) (s+1) (by simp [coeff_zero_eq_constantCoeff_apply,markerB,Nat.factorial_ne_zero])
    (sq_nonneg_coef j) (marker_square_partial hj _) (show (0:ℝ)≤s+4 by positivity)
    (fun _ ht ↦ w_delta ht)
  simp only [deltaSeq] at h
  exact ⟨(w_increment s).1.trans h.1,by linarith [h.2,(w_increment s).2]⟩

#print axioms raw_linear_bounds
#print axioms raw_quadratic_bounds
#print axioms raw_linear_increment
#print axioms raw_quadratic_increment
end OrderedPartitions.Kernel
