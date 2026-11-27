import OrderedPartitions.RenewalKernel

noncomputable section
namespace OrderedPartitions.Kernel

def gMain (s : ℕ) : ℝ := s+1+rho
def wMain (s : ℕ) : ℝ := (s+1:ℝ)*(s+2)/2 + 3*rho/2*(s+1)+rho^2

private theorem shifted_eps (s i : ℕ) : |eps (s+i)| * 8^s ≤ 1/(2*8^i) := by
  apply (le_div_iff₀ (by positivity)).mpr
  have h := (le_div_iff₀ (by positivity)).mp (eps_bound (s+i))
  rw [pow_add] at h
  linarith

private theorem line_pow (s : ℕ) : (s+1:ℝ) ≤ (2:ℝ)^s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    rw [pow_succ]; push_cast
    linarith [show (1:ℝ) ≤ 2^s by exact one_le_pow₀ (by norm_num)]

private theorem reduce_eight (s : ℕ) {a c r u : ℝ} (hr : 0<r) (hu : 0<u) (prod : r*u=8)
    (h : |a| *8^s ≤ c*u^s) : |a| ≤ c/r^s := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [← prod, mul_pow, ← mul_assoc] at h
  exact le_of_mul_le_mul_right h (pow_pos hu s)

theorem g_error (s : ℕ) : |g s-gMain s| ≤ (42/100:ℝ)/4^s := by
  obtain ⟨r0,r1⟩ := rho_interval
  have rp : 0 ≤ rho := by linarith
  apply reduce_eight s (r:=4) (u:=2) (by norm_num) (by norm_num) (by norm_num)
  have eqn : g s-gMain s = (s+1:ℝ)*eps (s+1)+rho*eps s := by rw [g_exact,gMain]; ring
  rw [eqn]
  apply (mul_le_mul_of_nonneg_right (abs_add_le ..) (show (0:ℝ) ≤ 8^s by positivity)).trans
  rw [add_mul, abs_mul, abs_mul, abs_of_nonneg rp, abs_of_nonneg (show (0:ℝ)≤s+1 by positivity),
    mul_assoc, mul_assoc]
  have e1 := shifted_eps s 1
  have e0 := shifted_eps s 0
  norm_num at e1 e0
  have l := line_pow s
  have o := one_le_pow₀ (show (1:ℝ)≤2 by norm_num) (n:=s)
  calc
    _ ≤ (s+1:ℝ)*(1/16)+rho*(1/2) := by gcongr
    _ ≤ _ := by linarith

theorem w_error (s : ℕ) : |w s-wMain s| ≤ (32/100:ℝ)/2^s := by
  obtain ⟨r0,r1⟩ := rho_interval
  have rp : 0 ≤ rho := by linarith
  let a : ℝ := (s+1:ℝ)*(s+2)/2
  let b : ℝ := 3*rho/2*(s+1)
  have a0 : 0≤a := by dsimp [a]; positivity
  have b0 : 0≤b := by dsimp [b]; positivity
  have eqn : w s-wMain s = a*eps (s+2)+b*eps (s+1)+rho^2*eps s := by
    rw [w_exact,wMain]; dsimp [a,b]; ring
  apply reduce_eight s (r:=2) (u:=4) (by norm_num) (by norm_num) (by norm_num)
  rw [eqn]
  have tri := (abs_add_le (a*eps (s+2)+b*eps (s+1)) (rho^2*eps s)).trans
    (add_le_add_left (abs_add_le _ _) _)
  apply (mul_le_mul_of_nonneg_right tri (show (0:ℝ)≤8^s by positivity)).trans
  simp only [add_mul, abs_mul, abs_of_nonneg a0, abs_of_nonneg b0,
    abs_of_nonneg (sq_nonneg rho), mul_assoc]
  have e2 := shifted_eps s 2
  have e1 := shifted_eps s 1
  have e0 := shifted_eps s 0
  norm_num at e2 e1 e0
  have l := line_pow s
  have l' : (2:ℝ)^s ≤ 4^s := by gcongr; norm_num
  have o := one_le_pow₀ (show (1:ℝ)≤4 by norm_num) (n:=s)
  have la : a ≤ (4:ℝ)^s := by
    have h2 : (s+2:ℝ) ≤ 2*2^s := by linarith [one_le_pow₀ (show (1:ℝ)≤2 by norm_num) (n:=s)]
    have z := mul_le_mul l h2 (by positivity) (by positivity)
    dsimp [a]
    rw [show (4:ℝ)^s=(2:ℝ)^s*2^s by rw [← mul_pow]; norm_num]
    linarith
  have lb : b ≤ 105/100*(4:ℝ)^s := by
    dsimp [b]
    have := mul_le_mul (show 3*rho/2≤105/100 by linarith) (l.trans l') (by positivity) (by norm_num)
    linarith
  calc
    _ ≤ a*(1/128)+b*(1/16)+rho^2*(1/2) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (show 0≤7/10-rho by linarith) (show 0≤7/10+rho by linarith)]

private theorem step_error (f main : ℕ → ℝ) (M r : ℝ) (hr : 0<r)
    (h : ∀ s, |f s-main s| ≤ M/r^s) (s : ℕ) :
    |(f (s+1)-f s) - (main (s+1)-main s)| ≤ (M+M/r)/r^s := by
  rw [show (f (s+1)-f s) - (main (s+1)-main s) = (f (s+1)-main (s+1))-(f s-main s) by ring]
  apply (abs_sub _ _).trans
  apply (add_le_add (h (s+1)) (h s)).trans
  rw [pow_succ]
  exact le_of_eq (by field_simp; ring)

theorem g_increment_error (s : ℕ) :
    |g (s+1)-g s-1| ≤ (525/1000:ℝ)/4^s := by
  have h := step_error g gMain (42/100) 4 (by norm_num) g_error s
  have hm : gMain (s+1)-gMain s=1 := by unfold gMain; push_cast; ring
  rw [hm] at h
  convert h using 2; norm_num

theorem w_increment_error (s : ℕ) :
    |w (s+1)-w s-(s+2+3*rho/2)| ≤ (48/100:ℝ)/2^s := by
  have h := step_error w wMain (32/100) 2 (by norm_num) w_error s
  have hm : wMain (s+1)-wMain s=s+2+3*rho/2 := by unfold wMain; push_cast; ring
  rw [hm] at h
  convert h using 2; norm_num

private theorem drop_decay {a M r : ℝ} (hm : 0≤M) (hr : 1≤r) (s : ℕ)
    (h : |a| ≤ M/r^s) : -M ≤ a ∧ a ≤ M := by
  exact abs_le.mp (h.trans (div_le_self hm (one_le_pow₀ hr)))

theorem g_bounds (s : ℕ) : (s+1:ℝ) ≤ g s ∧ g s ≤ s+3 := by
  have h := drop_decay (by norm_num) (by norm_num) s (g_error s)
  obtain ⟨hlo,hhi⟩ := rho_interval
  unfold gMain at h
  constructor <;> linarith [h.1,h.2]

theorem g_increment (s : ℕ) : 0 < g (s+1)-g s ∧ g (s+1)-g s < 2 := by
  have h := drop_decay (by norm_num) (by norm_num) s (g_increment_error s)
  constructor <;> linarith [h.1,h.2]

theorem w_bounds (s : ℕ) : ((s+1:ℝ)*(s+2)/2) ≤ w s ∧ w s ≤ (s+4)^2/2 := by
  have h := drop_decay (by norm_num) (by norm_num) s (w_error s)
  obtain ⟨hlo,hhi⟩ := rho_interval
  have hS : (0:ℝ) ≤ s := by positivity
  have rp : 0 ≤ rho := by linarith
  have hi := mul_le_mul_of_nonneg_right hhi.le (show 0≤(s:ℝ)+1 by positivity)
  have lo := mul_nonneg rp (show 0≤(s:ℝ)+1 by positivity)
  unfold wMain at h
  constructor
  · nlinarith [h.1, mul_nonneg (show 0≤rho-69/100 by linarith) (show 0≤rho+69/100 by linarith)]
  · nlinarith [h.2, mul_nonneg (show 0≤7/10-rho by linarith) (show 0≤7/10+rho by linarith)]

theorem w_increment (s : ℕ) : (s+2:ℝ) ≤ w (s+1)-w s ∧ w (s+1)-w s ≤ s+4 := by
  have h := drop_decay (by norm_num) (by norm_num) s (w_increment_error s)
  obtain ⟨hlo,hhi⟩ := rho_interval
  constructor <;> linarith [h.1,h.2]

#print axioms g_increment_error
#print axioms w_increment_error
#print axioms g_bounds
#print axioms w_bounds
#print axioms g_increment
#print axioms w_increment
#print axioms g_error
#print axioms w_error
end OrderedPartitions.Kernel
