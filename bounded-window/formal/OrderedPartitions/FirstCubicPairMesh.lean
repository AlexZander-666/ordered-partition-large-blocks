import OrderedPartitions.CubicPairSeparation
import OrderedPartitions.FirstCubicPairMoment

noncomputable section
open Polynomial
namespace OrderedPartitions.QuadraticOrder

/-- The fifth, one-sided test -J² supplies the far-left sign of the old row explicitly. -/
theorem first_cubic_mesh {J a b c d e f : ℝ} (j50 : 50≤J)
    (aL : 2*J≤a) (aU : a≤2.102*J)
    (bL : 0.49*J^2≤b) (bU : b≤0.607*J^2) (cL : 3≤c) (cU : c≤4)
    (dL : 0.99≤d) (dU : d≤1.04) (eL : J+1.9≤e) (eU : e≤1.124*J)
    (fL : 4≤f) (fU : f≤9) :
    ThreeToThree (cubic 1 a b c) (cubic 1 (a+d) (b+e) (c+f)) := by
  let P := cubic 1 a b c
  let H := quadratic d e f
  let Q := cubic 1 (a+d) (b+e) (c+f)
  have jp : 0<J := by linarith
  have jp2 : 0<J^2 := by positivity
  have jp3 : 0<J^3 := by positivity
  have jp4 : 0<J^4 := by positivity
  have jp6 : 0<J^6 := by positivity
  have JJ : 50*J≤J^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr j50) jp.le]
  have aa : 0≤a := by linarith
  have cc : 0≤c := by linarith
  have ff : 0≤f := by linarith
  let u := 1/J
  have up : 0<u := by dsimp [u]; positivity
  have Ju : J*u=1 := by dsimp [u]; field_simp
  have uU : u≤1/50 := (div_le_iff₀ jp).mpr (by linarith)
  have sqU : u^2 ≤ (1/50:ℝ)^2 := pow_le_pow_left₀ up.le uU _
  have au : 2 ≤ a*u := by nlinarith only [mul_le_mul_of_nonneg_right aL up.le,Ju]
  have bu : b*u^2 ≤ 0.607 := by
    calc
      _ ≤ (0.607*J^2)*u^2 := mul_le_mul_of_nonneg_right bU (sq_nonneg _)
      _ = 0.607*(J*u)^2 := by ring
      _ = _ := by rw [Ju]; norm_num
  have eu1 : 1 ≤ e*u := by nlinarith only [mul_le_mul_of_nonneg_right eL up.le,Ju,up]
  have eu2 : e*u ≤ 1.124 := by nlinarith only [mul_le_mul_of_nonneg_right eU up.le,Ju]
  have fu : f*u^2 ≤ 9*(1/50:ℝ)^2 :=
    mul_le_mul fU sqU (sq_nonneg _) (by norm_num)
  have cu : 0≤c*u^3 := by positivity
  have pd : P.natDegree≤3 := by unfold P cubic quadratic; compute_degree!
  have qd : Q.natDegree≤3 := by unfold Q cubic quadratic; compute_degree!
  apply divided_difference_mesh (P:=P) (Q:=Q) (d:=d) (e:=e) (f:=f)
    (by linarith) pd qd (by simp [P]) (by intro x; simp [P,Q]; ring)
    (t:= -(J^2)) (A:= -J) (B:= -1) (C:= -2*u) (D:= -(4/5)*u)
    (by nlinarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · simp only [P,eval_cubic]
    have a2 := mul_nonneg aa jp2.le
    have b4 := mul_le_mul_of_nonneg_right bU jp4.le
    have c6 := mul_le_mul_of_nonneg_right cL jp6.le
    have one6 : 1≤J^6 := one_le_pow₀ (by linarith)
    nlinarith only [a2,b4,c6,one6]
  · simp only [P,eval_cubic]
    have a1 := mul_le_mul_of_nonneg_right aU jp.le
    have b2 := mul_le_mul_of_nonneg_right bL jp2.le
    have c3 := mul_le_mul_of_nonneg_right cU jp3.le
    have z : 0≤J^2*(0.49*J^2-4*J-2.102) := mul_nonneg jp2.le (by linarith)
    nlinarith only [a1,b2,c3,z]
  · simp only [P,eval_cubic]
    nlinarith only [aU,bL,cU,JJ,j50]
  · simp only [P,eval_cubic]
    nlinarith only [au,bu,cu]
  · simp only [P,eval_cubic]
    nlinarith only [au,bu,cu]
  · simp only [eval_quadratic]
    have e1 := mul_le_mul_of_nonneg_right eU jp.le
    have f2 := mul_le_mul_of_nonneg_right fL jp2.le
    nlinarith only [e1,f2,dL,jp2]
  · simp only [eval_quadratic]
    nlinarith only [dU,eL,fU,j50]
  · simp only [eval_quadratic]
    nlinarith only [dU,eu1,fu]
  · simp only [eval_quadratic]
    nlinarith only [dL,eu2,mul_nonneg ff (sq_nonneg u)]

#print axioms first_cubic_mesh
end OrderedPartitions.QuadraticOrder
