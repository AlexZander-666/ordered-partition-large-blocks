import OrderedPartitions.QuadraticActual

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

def v (s : ℕ) : ℝ := coeff s (K^4)
def vMain (s : ℕ) : ℝ := (s+1:ℝ)*(s+2)*(s+3)/6 + rho*(s+1)*(s+2) +
  11/6*rho^2*(s+1)+rho^3

theorem v_exact (s : ℕ) : v s =
    (s+1:ℝ)*(s+2)*(s+3)/6*(1+eps (s+3)) +
    rho*(s+1)*(s+2)*(1+eps (s+2)) + 11/6*rho^2*(s+1)*(1+eps (s+1)) +
    rho^3*(1+eps s) := by
  have eqn : derivative ℝ (K^3) = C (3:ℝ)*K^4-C (3*rho)*K^3 := by
    rw [derivative_pow,K_derivative]
    simp only [show (3:ℝ)=1+1+1 by norm_num,map_add,map_one,map_mul]
    norm_num
    ring
  have coef := congrArg (coeff s) eqn
  simp only [coeff_derivative,map_sub,coeff_C_mul] at coef
  change w (s+1)*(s+1:ℝ) = 3*v s-(3*rho)*w s at coef
  rw [w_exact,w_exact] at coef
  push_cast at coef
  linarith only [coef]

private theorem eps_weight {s d : ℕ} {a U : ℝ} (az : 0≤a) (bound : a≤U*8^s) :
    |a*eps (s+d)| ≤ U/(2*8^d) := by
  rw [abs_mul,abs_of_nonneg az]
  have h := mul_le_mul bound (eps_bound (s+d)) (abs_nonneg _)
    (az.trans bound)
  apply h.trans
  rw [pow_add]
  exact le_of_eq (by field_simp)

private theorem poly_weights (s : ℕ) :
    (s+1:ℝ)*(s+2)*(s+3)/6 ≤ 8^s ∧ (s+1:ℝ)*(s+2)≤2*8^s ∧ (s+1:ℝ)≤8^s := by
  have l : (s+1:ℝ) ≤ (2:ℝ)^s := by
    induction s with
    | zero => norm_num
    | succ s ih =>
      rw [pow_succ];push_cast
      linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=s)]
  have o := one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=s)
  have l2 : (s+2:ℝ)≤2*(2:ℝ)^s := by linarith
  have l3 : (s+3:ℝ)≤3*(2:ℝ)^s := by linarith
  have a := mul_le_mul l l2 (by positivity) (by positivity)
  have b := mul_le_mul a l3 (by positivity) (by positivity)
  have e : (8:ℝ)^s = (2^s:ℝ)^3 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have sq8 : (2^s:ℝ)^2 ≤ 8^s := by rw [e]; exact pow_le_pow_right₀ o (by decide)
  refine ⟨?_,?_,l.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)⟩
  · rw [e]; nlinarith only [b]
  · nlinarith only [a,sq8]

theorem v_error (s : ℕ) : |v s-vMain s| ≤ 0.24 := by
  obtain ⟨a,b,c⟩ := poly_weights s
  obtain ⟨r0,r1⟩ := rho_interval
  have rp : 0≤rho := by linarith
  have sq := pow_le_pow_left₀ rp r1.le 2
  have cube := pow_le_pow_left₀ rp r1.le 3
  let A : ℝ := (s+1:ℝ)*(s+2)*(s+3)/6
  let B : ℝ := rho*(s+1)*(s+2)
  let C : ℝ := 11/6*rho^2*(s+1)
  have uA := eps_weight (s:=s) (d:=3) (a:=A) (U:=1) (by dsimp [A]; positivity) (by simpa [A] using a)
  have uB := eps_weight (s:=s) (d:=2) (a:=B) (U:=1.4) (by dsimp [B]; positivity) (by
    dsimp [B]; rw [mul_assoc]
    have h := mul_le_mul r1.le b (by positivity) (by norm_num)
    linarith only [h])
  have uC := eps_weight (s:=s) (d:=1) (a:=C) (U:=11/6*(0.7)^2) (by dsimp [C]; positivity) (by
    dsimp [C]; gcongr; linarith)
  have uD := eps_weight (s:=s) (d:=0) (a:=rho^3) (U:=(0.7)^3) (by positivity) (by
    exact cube.trans (by nlinarith only [one_le_pow₀ (by norm_num : (1:ℝ)≤8) (n:=s)]))
  simp only [Nat.add_zero] at uD
  have eqn : v s-vMain s =
    A*eps (s+3)+B*eps (s+2)+C*eps (s+1)+rho^3*eps s := by
    rw [v_exact,vMain];dsimp [A,B,C];ring
  rw [eqn]
  have t1 := abs_add_le (A*eps (s+3)) (B*eps (s+2))
  have t2 := abs_add_le (A*eps (s+3)+B*eps (s+2)) (C*eps (s+1))
  have t3 := abs_add_le (A*eps (s+3)+B*eps (s+2)+C*eps (s+1)) (rho^3*eps s)
  linarith only [uA,uB,uC,uD,t1,t2,t3]

def vUpper (x : ℝ) := x^3/6+1.7*x^2+4.84*x+3.89
def dvLower (x : ℝ) := x^2/2+3.87*x+6
def dvUpper (x : ℝ) := x^2/2+3.9*x+7.30

theorem v_range (s : ℕ) : (s:ℝ)^3/6 ≤ v s ∧ v s ≤ vUpper s := by
  obtain ⟨rl,ru⟩ := rho_interval
  have e := abs_le.mp (v_error s)
  have rp : 0≤rho := by linarith
  have a := mul_le_mul_of_nonneg_right ru.le (show (0:ℝ)≤(s+1:ℝ)*(s+2) by positivity)
  have b := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ rp ru.le 2) (show (0:ℝ)≤(s+1:ℝ) by positivity)
  have d := pow_le_pow_left₀ rp ru.le 3
  unfold vMain vUpper at *
  constructor
  · nlinarith only [e.1,mul_nonneg rp (show (0:ℝ)≤(s+1:ℝ)*(s+2) by positivity),
      mul_nonneg (sq_nonneg rho) (show (0:ℝ)≤s+1 by positivity),pow_nonneg rp 3,Nat.cast_nonneg (α:=ℝ) s,sq_nonneg (s:ℝ)]
  · nlinarith only [e.2,a,b,d,Nat.cast_nonneg (α:=ℝ) s]

theorem dv_range (s : ℕ) : dvLower s ≤ v (s+1)-v s ∧ v (s+1)-v s ≤ dvUpper s := by
  obtain ⟨rl,ru⟩ := rho_interval
  have rp : 0≤rho := by linarith
  have e := abs_le.mp (v_error s)
  have e' := abs_le.mp (v_error (s+1))
  have de : vMain (s+1)-vMain s = (s+2:ℝ)*(s+3)/2+2*rho*(s+2)+11/6*rho^2 := by
    unfold vMain; push_cast; ring
  have nn : (0:ℝ)≤s+2 := by positivity
  unfold dvLower dvUpper
  constructor
  · nlinarith only [de, e.2, e'.1,mul_le_mul_of_nonneg_right rl.le nn,
      pow_le_pow_left₀ (by norm_num) rl.le 2,Nat.cast_nonneg (α:=ℝ) s]
  · nlinarith only [de, e.1, e'.2,mul_le_mul_of_nonneg_right ru.le nn,
      pow_le_pow_left₀ rp ru.le 2,Nat.cast_nonneg (α:=ℝ) s]

#print axioms v_exact
#print axioms v_error
#print axioms v_range
#print axioms dv_range
end OrderedPartitions.Kernel
