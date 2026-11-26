import OrderedPartitions.MeanKernel
import OrderedPartitions.FirstJumpCriterion
import OrderedPartitions.QuadraticExactRows
noncomputable section
open PowerSeries Finset
namespace OrderedPartitions.Kernel

private theorem upper_k {n : ℕ} (hn : 2≤n) : coeff n K ≤ 129/128 := by
  have e := (abs_le.mp (eps_bound n)).2
  have pw : (64:ℝ)≤8^n := (show (64:ℝ)=8^2 by norm_num).trans_le (pow_le_pow_right₀ (by norm_num) hn)
  have up : (1:ℝ)/(2*8^n)≤1/128 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  unfold eps at e
  linarith

private theorem lower_marked {j n : ℕ} (hj : j ≤ n) :
    Renewal.q rho j * ((n-j:ℕ)+1) ≤ coeff n (big j*K^2) := by
  have rp : 0<rho := by linarith [rho_interval.1]
  have non (r : ℕ) : 0≤coeff r (big j) := by rw [big_coeff]; split_ifs <;> positivity
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change _ ≤ ∑ r ∈ range (n+1), coeff r (big j)*g (n-r)
  have single := single_le_sum (f:=fun r ↦ coeff r (big j)*g (n-r)) (s:=range (n+1))
    (fun r _ ↦ mul_nonneg (non _) (by linarith [(g_bounds (n-r)).1, Nat.cast_nonneg (α:=ℝ) (n-r)]))
    (mem_range.mpr (Nat.lt_succ_of_le hj))
  apply le_trans _ single
  rw [big_coeff, if_pos (le_refl _)]
  exact mul_le_mul_of_nonneg_left (g_bounds _).1 (by unfold Renewal.q; positivity)

private theorem normalized_second {j : ℕ} (hj : 1≤j) :
    (row (2*j) j).coeff 2 / (row (2*j) j).eval 1 =
      (2*rho)*(Renewal.q rho j)^2/coeff (2*j) K := by
  rw [coeff_row hj, first_jump_count hj, k_row hj, Nat.cast_choose ℝ (show j≤2*j by omega)]
  have rp : 0<rho := by linarith [rho_interval.1]
  have v := original_eval_pos hj (2*j)
  rw [show 2*j-j=j by omega]
  unfold Renewal.q
  rw [show rho^(2*j) = (rho^j)^2 by rw [← pow_mul]; congr 1; omega]
  field_simp

private theorem normalized_mean {j : ℕ} (hj : 1≤j) (n : ℕ) :
    markedMean (row n j) = coeff n (big j*K^2)/((2*rho)*coeff n K) := by
  have rp : 0<rho := by linarith [rho_interval.1]
  have v := original_eval_pos hj n
  rw [markedMean, g_marked hj, k_row hj]
  field_simp

theorem first_jump_large {j : ℕ} (hj : 7≤j) :
    let p := row (2*j-1) j
    let q := row (2*j) j
    q.coeff 2/q.eval 1 < markedMean p*(markedMean q-markedMean p) := by
  let n := 2*j-1
  let u := Renewal.q rho j
  let x := coeff n (big j*K^2)
  let y := coeff (n+1) (big j*K^2)
  let a := coeff n K
  let b := coeff (n+1) K
  have j1 : 1≤j := by omega
  have hn : j≤n := by dsimp [n]; omega
  have hn' : n+1=2*j := by dsimp [n]; omega
  have rpos : 0<rho := by linarith [rho_interval.1]
  have up : 0<u := by dsimp [u,Renewal.q]; positivity
  have ap : 0<a := k_pos _
  have bp : 0<b := k_pos _
  have ua : a≤129/128 := upper_k (show 2≤n by omega)
  have excess : 0 < coeff j (big j) := by rw [big_coeff,if_pos (le_refl _)]; positivity
  have det : (2/5)*u < a*y-b*x := by
    have h := convolution_barrier (by omega : 2≤n) hn (big j)
      (fun r ↦ by rw [big_coeff]; split_ifs <;> positivity) excess
    rw [big_coeff,if_pos (le_refl _)] at h
    exact h
  have xl : (j:ℝ)*u≤x := by
    have h := lower_marked hn
    have idx : n-j+1 = j := by dsimp [n]; omega
    have idx' : ((n-j:ℕ):ℝ)+1=j := by exact_mod_cast idx
    rw [idx',mul_comm] at h
    exact h
  have jge : (7:ℝ)≤j := by exact_mod_cast hj
  have dpos : 0 < a*y-b*x := by linarith
  have mass : (7*u)*((2/5)*u) < x*(a*y-b*x) := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg
    ((mul_le_mul_of_nonneg_right jge up.le).trans xl) det (by positivity) (by positivity)
  have rc : 2*rho ≤ 7/5 := by linarith [rho_interval.2]
  have c3 := pow_le_pow_left₀ (by positivity : 0≤2*rho) rc 3
  have a2 := pow_le_pow_left₀ ap.le ua 2
  have major : (2*rho)^3*a^2 < 7*(2/5:ℝ) :=
    lt_of_le_of_lt (mul_le_mul c3 a2 (by positivity) (by positivity)) (by norm_num)
  have signed : (2*rho)^3*a^2*u^2 < x*(a*y-b*x) := by
    have bound := mul_lt_mul_of_pos_right major (sq_pos_of_pos up)
    nlinarith only [bound,mass]
  dsimp only
  rw [normalized_second j1, normalized_mean j1, normalized_mean j1]
  change (2*rho)*u^2/coeff (2*j) K < x/((2*rho)*a) *
    (coeff (2*j) (big j*K^2)/((2*rho)*coeff (2*j) K)-x/((2*rho)*a))
  rw [← hn']
  change (2*rho)*u^2/b < x/((2*rho)*a)*(y/((2*rho)*b)-x/((2*rho)*a))
  field_simp
  linarith only [signed]

theorem first_jump_moment {j : ℕ} (hj : 2≤j) :
    let p := row (2*j-1) j
    let q := row (2*j) j
    q.coeff 2/q.eval 1 < markedMean p*(markedMean q-markedMean p) := by
  by_cases h : 7≤j
  · exact first_jump_large h
  have hi : j≤6 := by omega
  interval_cases j
  · change (row 4 2).coeff 2/(row 4 2).eval 1 < _
    have hp : QuadraticExact.coefficientRow 2 3 = ⟨6, 7, 0, 0⟩ := by decide +kernel
    have hq : QuadraticExact.coefficientRow 2 4 = ⟨24, 45, 6, 0⟩ := by decide +kernel
    rw [QuadraticExact.original_row (j:=2) (n:=4) (by decide) (by decide),
      QuadraticExact.original_row (j:=2) (n:=3) (by decide) (by decide), hp, hq]
    norm_num [QuadraticExact.Coefficients.polynomial, markedMean, Polynomial.coeff_X]
  · change (row 6 3).coeff 2/(row 6 3).eval 1 < _
    have hp : QuadraticExact.coefficientRow 3 5 = ⟨450, 91, 0, 0⟩ := by decide +kernel
    have hq : QuadraticExact.coefficientRow 3 6 = ⟨3690, 973, 20, 0⟩ := by decide +kernel
    rw [QuadraticExact.original_row (j:=3) (n:=6) (by decide) (by decide),
      QuadraticExact.original_row (j:=3) (n:=5) (by decide) (by decide), hp, hq]
    norm_num [QuadraticExact.Coefficients.polynomial, markedMean, Polynomial.coeff_X]
  · change (row 8 4).coeff 2/(row 8 4).eval 1 < _
    have hp : QuadraticExact.coefficientRow 4 7 = ⟨45570, 1723, 0, 0⟩ := by decide +kernel
    have hq : QuadraticExact.coefficientRow 4 8 = ⟨521640, 24125, 70, 0⟩ := by decide +kernel
    rw [QuadraticExact.original_row (j:=4) (n:=8) (by decide) (by decide),
      QuadraticExact.original_row (j:=4) (n:=7) (by decide) (by decide), hp, hq]
    norm_num [QuadraticExact.Coefficients.polynomial, markedMean, Polynomial.coeff_X]
  · change (row 10 5).coeff 2/(row 10 5).eval 1 < _
    have hp : QuadraticExact.coefficientRow 5 9 = ⟨7044450, 42811, 0, 0⟩ := by decide +kernel
    have hq : QuadraticExact.coefficientRow 5 10 = ⟨101519250, 728061, 252, 0⟩ := by decide +kernel
    rw [QuadraticExact.original_row (j:=5) (n:=10) (by decide) (by decide),
      QuadraticExact.original_row (j:=5) (n:=9) (by decide) (by decide), hp, hq]
    norm_num [QuadraticExact.Coefficients.polynomial, markedMean, Polynomial.coeff_X]
  · change (row 12 6).coeff 2/(row 12 6).eval 1 < _
    have hp : QuadraticExact.coefficientRow 6 11 = ⟨1621316466, 1316107, 0, 0⟩ := by decide +kernel
    have hq : QuadraticExact.coefficientRow 6 12 = ⟨28065324210, 26242461, 924, 0⟩ := by decide +kernel
    rw [QuadraticExact.original_row (j:=6) (n:=12) (by decide) (by decide),
      QuadraticExact.original_row (j:=6) (n:=11) (by decide) (by decide), hp, hq]
    norm_num [QuadraticExact.Coefficients.polynomial, markedMean, Polynomial.coeff_X]

theorem original_first_jump {j : ℕ} (hj : 2≤j) :
    let p := row (2*j-1) j
    let q := row (2*j) j
    ∃ l m r : ℝ, l < m ∧ m < r ∧ r < 0 ∧ p.IsRoot m ∧
      ∀ x : ℝ, q.eval x = q.coeff 2 * (x-l) * (x-r) :=
  (original_first_jump_iff hj).mp (first_jump_moment hj)

#print axioms original_first_jump
#print axioms first_jump_moment
#print axioms first_jump_large
end OrderedPartitions.Kernel
