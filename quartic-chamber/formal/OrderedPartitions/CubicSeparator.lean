import OrderedPartitions.CubicPairSeparation

/-! A positive quadratic Euclidean remainder separates two cubic rows. -/

noncomputable section
open Polynomial
namespace OrderedPartitions.QuadraticOrder

/-- If the quadratic difference hP−gQ strictly separates a cubic P, then Q has
alternating signs at all three old roots. A positive value of the difference
at zero fixes the orientation, with no need to approximate the cubic roots. -/
theorem signed_from_quadratic_separator {p q : ℝ[X]} {g h : ℝ} (hg : 0 < g)
    (hconst : 0 < (C h*p-C g*q).eval 0) (roots : TwoToThree (C h*p-C g*q) p) :
    ∃ x y z : ℝ, x < y ∧ y < z ∧ z < 0 ∧ ExactRoots p [x,y,z] ∧
      q.eval x < 0 ∧ 0 < q.eval y ∧ q.eval z < 0 := by
  let R := C h*p-C g*q
  obtain ⟨x,l,y,r,z,hxl,hly,hyr,hrz,hz,hR,hP⟩ := roots
  have fac (v : ℝ) : R.eval v = R.leadingCoeff * (v-l) * (v-r) := by
    have E := congrArg (Polynomial.eval v) hR.factor
    simpa [R, mul_assoc] using E
  have r0 := hrz.trans hz
  have l0 := hly.trans (hyr.trans r0)
  have coefpos : 0 < R.leadingCoeff := by
    change 0 < R.eval 0 at hconst
    rw [fac, mul_pos_iff_of_pos_right (by linarith : 0 < 0-r),
      mul_pos_iff_of_pos_right (by linarith : 0 < 0-l)] at hconst
    exact hconst
  have eqv (v : ℝ) (hv : p.eval v = 0) : R.eval v = -g*q.eval v := by
    simp [R,hv,neg_mul]
  have zeros (v : ℝ) (hv : v ∈ [x,y,z]) : p.eval v = 0 := by
    have E := congrArg (Polynomial.eval v) hP.factor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> simpa using E
  have X := fac x
  have Y := fac y
  have Z := fac z
  rw [eqv x (zeros x (by simp))] at X
  rw [eqv y (zeros y (by simp))] at Y
  rw [eqv z (zeros z (by simp))] at Z
  refine ⟨x,y,z,hxl.trans hly,hyr.trans hrz,hz,hP,?_,?_,?_⟩
  · have pos := mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg coefpos (sub_neg.mpr hxl))
      (sub_neg.mpr (hxl.trans (hly.trans hyr)))
    rw [← X,neg_mul,neg_pos] at pos
    by_contra! nonneg
    exact (not_lt_of_ge (mul_nonneg hg.le nonneg)) pos
  · have neg := mul_neg_of_pos_of_neg (mul_pos coefpos (sub_pos.mpr hly)) (sub_neg.mpr hyr)
    rw [← Y,neg_mul,neg_lt_zero] at neg
    exact (mul_pos_iff_of_pos_left hg).mp neg
  · have pos := mul_pos (mul_pos coefpos (sub_pos.mpr (hly.trans (hyr.trans hrz)))) (sub_pos.mpr hrz)
    rw [← Z,neg_mul,neg_pos] at pos
    by_contra! nonneg
    exact (not_lt_of_ge (mul_nonneg hg.le nonneg)) pos

/-- A quadratic difference with two roots strictly between the old cubic roots
suffices for the full alternating root lists. -/
theorem three_to_three_of_separator {p q : ℝ[X]} {g h : ℝ} (hg : 0 < g)
    (hconst : 0 < (C h*p-C g*q).eval 0) (roots : TwoToThree (C h*p-C g*q) p)
    (q0 : 0 < q.eval 0) (qd : q.natDegree ≤ 3) : ThreeToThree p q := by
  obtain ⟨x,y,z,xy,yz,z0,hp,qx,qy,qz⟩ := signed_from_quadratic_separator hg hconst roots
  exact threeToThree_of_signs hp xy yz z0 qx qy qz q0 qd

#print axioms three_to_three_of_separator
#print axioms signed_from_quadratic_separator
end OrderedPartitions.QuadraticOrder
