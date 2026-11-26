import OrderedPartitions.CubicFiniteSigns
import OrderedPartitions.CubicQuarticNormalized
import OrderedPartitions.CubicSeparator

/-! Transfer the signed integer test to the exact cubic and quartic root lists. -/

open Polynomial

noncomputable section

namespace OrderedPartitions.CubicFinite

open QuadraticExact QuadraticOrder

/-- The quadratic separator certifies the roots of the old row. The quartic
subtraction is a multiple of that old row and vanishes at every old root. -/
theorem adjacent_of_signs {jump : Prop} {a b c d e f g h k : ℝ}
    (certificate : signs jump a b c d e f g h k) (k_nonneg : 0 ≤ k) :
    CubicAdjacent (cubic a b c d) (quartic e f g h k) jump := by
  let P := cubic a b c d
  let Q := quartic e f g h k
  let z := d*h-k*c
  let A := z*a-d*d*e
  let B := d*k*a+z*b-d*d*f
  let C₂ := d*k*b+z*c-d*d*g
  let R := quadratic A B C₂
  let Qscaled := C (d*d)*Q-C (d*k)*X*P
  have expansion : C z*P-C (1 : ℝ)*Qscaled = R := by
    simp only [Qscaled, P, Q, R, quartic, cubic, quadratic, A, B, C₂, z,
      map_sub, map_mul, map_add, map_one]
    ring
  obtain ⟨he, hk, test⟩ := certificate
  change inequalities True A B C₂ a b c d at test
  obtain ⟨hA, hB, hC, ha, _, _, hd, hu, hv⟩ := test
  have hdpos : 0 < d := hd.mpr trivial
  have order : TwoToThree R P :=
    ((QuadraticOrder.adjacent_of_remainder (e := b) (f := c) hA hB hC ha hdpos.le
      hu hv).resolve_right (fun bad ↦ bad.1 hdpos)).2
  have hconstant : 0 < (C z*P-C (1 : ℝ)*Qscaled).eval 0 := by
    rw [expansion]
    simpa [R] using hA
  have bracket : TwoToThree (C z*P-C (1 : ℝ)*Qscaled) P := by
    rwa [expansion]
  obtain ⟨x,y,w,xy,yw,wneg,roots,sx,sy,sw⟩ :=
    signed_from_quadratic_separator (by norm_num : (0 : ℝ) < 1) hconstant bracket
  have eval_scaled (v : ℝ) (mem : v ∈ [x,y,w]) : Qscaled.eval v = d*d*Q.eval v := by
    have root : P.eval v = 0 := by
      rw [roots.factor]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> simp
    simp [Qscaled, root]
  rw [eval_scaled x (by simp)] at sx
  rw [eval_scaled y (by simp)] at sy
  rw [eval_scaled w (by simp)] at sw
  have pos := mul_pos hdpos hdpos
  have sx' : Q.eval x < 0 := by
    apply lt_of_mul_lt_mul_left (a := d*d) _ pos.le
    simpa only [mul_zero] using sx
  have sy' := (mul_pos_iff_of_pos_left pos).mp sy
  have sw' : Q.eval w < 0 := by
    apply lt_of_mul_lt_mul_left (a := d*d) _ pos.le
    simpa only [mul_zero] using sw
  have q0 : 0 < Q.eval 0 := by simpa [Q] using he
  by_cases step : jump
  · have kp := hk.mpr step
    have shape := quartic_leading (a := e) (b := f) (c := g) (d := h) kp.ne'
    exact Or.inl ⟨step, three_to_four_of_signs roots xy yw wneg sx' sy' sw' q0
      shape.1 (shape.2.symm ▸ kp)⟩
  · have kz : k = 0 := le_antisymm (le_of_not_gt (fun hp ↦ step (hk.mp hp))) k_nonneg
    have degree : Q.natDegree ≤ 3 := by
      unfold Q quartic cubic quadratic
      rw [kz]
      simp
      compute_degree!
    exact Or.inr ⟨step, threeToThree_of_signs roots xy yw wneg sx' sy' sw' q0 degree⟩

private theorem row_quartic {j n : ℕ} (hj : 1 ≤ j) (hn : n ≤ 4*j) :
    row n j = quartic ((row n j).coeff 0) ((row n j).coeff 1) ((row n j).coeff 2)
      ((row n j).coeff 3) ((row n j).coeff 4) := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [quartic, cubic, quadratic, coeff_X]
  · have hmul : 5*j ≤ i*j := Nat.mul_le_mul_right j (by omega)
    have hz : count n j i = 0 := count_above_degree hj (by omega)
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h4 : i ≠ 4 := by omega
    simp [quartic, cubic, quadratic, coeff_row hj, coeff_X, hz, h0, Ne.symm h1,
      h2, h3, h4]

/-- An exact cutoff check implies strict alternation for the original counted rows. -/
theorem original_of_check {j n : ℕ} (hj : 1 ≤ j) (lo : 3*j ≤ n) (hi : n < 4*j)
    (passed : checkCutoff j = true) :
    CubicAdjacent (row n j) (row (n+1) j) (n+1 = 4*j) := by
  have sign := checkCutoff_sound hj lo hi passed
  have q4 : 0 ≤ (row (n+1) j).coeff 4 := by rw [coeff_row hj]; positivity
  have p4 : (row n j).coeff 4 = 0 := by rw [coeff_row hj, count_above_degree hj hi]; simp
  have old :
      row n j = cubic ((row n j).coeff 0) ((row n j).coeff 1) ((row n j).coeff 2)
        ((row n j).coeff 3) := by
    conv_lhs => rw [row_quartic hj hi.le]
    simp [quartic, p4]
  have result := adjacent_of_signs sign q4
  rwa [← old, ← row_quartic hj (by omega : n+1 ≤ 4*j)] at result

#print axioms adjacent_of_signs
#print axioms original_of_check

end OrderedPartitions.CubicFinite
