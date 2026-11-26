import OrderedPartitions.RenewalMajorants

noncomputable section
open Finset PowerSeries
namespace OrderedPartitions.Renewal

/-- The true exponential tail, including its lower endpoint. -/
def expTail (a : ℝ) (l : ℕ) : ℝ := ∑' u : ℕ, q a (u+l)

/-- Each retained tap is weighted at its own degree. The positive tail starts at N+1-i+d. -/
def tailCost (rho R c : ℝ) (N d : ℕ) : ℝ :=
  ∑ i ∈ range (N+1), (|coeff i (seriesT rho N)| * R^i) *
    (c/R^d * expTail (R*rho) (N+1-i+d))

private theorem weighted_q_shift (rho : ℝ) {R : ℝ} (hR : 0 < R) (c : ℝ) {i v : ℕ}
    (hi : i ≤ v) (d : ℕ) : c*q rho (v-i+d)*R^v = R^i*(c/R^d*q (R*rho) (v-i+d)) := by
  have he : i+(v-i)=v := by omega
  rw [show R^v = R^i * R^(v-i) by rw [← pow_add, he]]
  simp only [q, mul_pow, pow_add]
  field_simp

private theorem conv_point {rho R c : ℝ} {N v d : ℕ} (hr : 0 < R) (hv : N ≤ v)
    (S : PowerSeries ℝ) (hs : ∀ n, |coeff n S| ≤ c*q rho (n+d)) :
    |coeff v (seriesT rho N * S)| * R^v ≤ ∑ i ∈ range (N+1),
      (|coeff i (seriesT rho N)| * R^i) * (c/R^d*q (R*rho) (v-i+d)) := by
  rw [truncated_product_coeff rho hv]
  apply le_trans (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hr.le _))
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  rw [abs_mul, mul_assoc]
  have hil := mem_range.mp hi
  have e := weighted_q_shift rho hr c (show i ≤ v by omega) d
  calc
    _ ≤ |coeff i (seriesT rho N)| * ((c*q rho (v-i+d))*R^v) := by gcongr; exact hs _
    _ = _ := by rw [e]; ring

theorem convolution_tail_bound {rho R c : ℝ} (h0 : 0 ≤ rho) (hr : 0 < R) (hc : 0 ≤ c)
    (N d K : ℕ) (S : PowerSeries ℝ) (hs : ∀ n, |coeff n S| ≤ c*q rho (n+d)) :
    (∑ u ∈ range K, |coeff (N+1+u) (seriesT rho N*S)| * R^(N+1+u)) ≤ tailCost rho R c N d := by
  calc
    _ ≤ ∑ u ∈ range K, ∑ i ∈ range (N+1),
        (|coeff i (seriesT rho N)| * R^i) *
        (c/R^d*q (R*rho) (N+1+u-i+d)) :=
      sum_le_sum (fun u _ ↦ conv_point hr (by omega) S hs)
    _ = ∑ i ∈ range (N+1), (|coeff i (seriesT rho N)| * R^i) *
        (c/R^d * ∑ u ∈ range K, q (R*rho) (u+(N+1-i+d))) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      have hle := mem_range.mp hi
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro u _
      rw [show N+1+u-i+d=u+(N+1-i+d) by omega]
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ((summable_nat_add_iff _).mpr (q_hasSum (R*rho)).summable).sum_le_tsum _
        (fun u _ ↦ by unfold q; positivity)

theorem residual_prefix_bound {rho R : ℝ} (he : Real.exp rho = 2)
    (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (hr : 0 < R) {N n : ℕ} (hn : N ≤ n) :
    (∑ i ∈ range n, |coeff (i+1) (residualP rho N)| * R^(i+1)) ≤ tailCost rho R 2 N 1 := by
  obtain ⟨K,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [sum_range_add]
  have head : (∑ i ∈ range N, |coeff (i+1) (residualP rho N)| * R^(i+1)) = 0 :=
    sum_eq_zero (fun i hi ↦ by rw [residualP_early rho (mem_range.mp hi)]; simp)
  rw [head, zero_add]
  calc
    _ = ∑ u ∈ range K, |coeff (N+1+u) (seriesT rho N*factorB rho)| * R^(N+1+u) := by
      apply sum_congr rfl
      intro u _
      rw [show N+u+1=N+1+u by omega, residualP, map_sub, coeff_one, if_neg (by omega)]
      simp
    _ ≤ _ := convolution_tail_bound h0 hr (by norm_num) _ _ _ _ (fun n ↦ by
      obtain ⟨hx, hb⟩ := factorB_bounds he h0 h1 n
      simpa [abs_of_nonneg hx] using hb)

theorem forcing_point_bound {rho R : ℝ} (he : Real.exp rho = 2)
    (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (hr : 0 < R) {N n : ℕ} (hn : N < n) :
    |coeff n (forcedD rho N)| * R^n ≤ tailCost rho R 4 N 2 := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hn
  refine (single_le_sum (f := fun k ↦ |coeff (N+1+k) (seriesT rho N*forcingJ rho)| *
    R^(N+1+k)) (s := range (u+1)) (fun k _ ↦ by positivity) (mem_range.mpr (by omega))).trans ?_
  exact convolution_tail_bound h0 hr (by norm_num) _ _ _ _ (fun n ↦ by
    obtain ⟨hx,hb⟩ := forcingJ_bounds he h0 h1 n
    simpa [abs_of_nonneg hx] using hb)

/-- At the paper's cutoff and radius only the finite initial data and two scalar tail costs remain. -/
theorem ordered_bell_error_of_three_checks
    (initial : ∀ n ≤ 48, |coeff n (errorE (Real.log 2))| * 8^n ≤ (1/2:ℝ))
    (residual : tailCost (Real.log 2) 8 2 48 1 ≤ 697279/1000000)
    (forcing : tailCost (Real.log 2) 8 4 48 2 ≤ 131844/1000000)
    {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    |2 * (Real.log 2)^(n+1) * (row n j).eval 1/n.factorial-1| ≤ 1/(2*8^n) := by
  have he : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have estimate := original_error_of_budget (Real.log 2) 48 8 (1/2) (by norm_num) initial
    (fun m hm ↦ by
      have r := (residual_prefix_bound he h0 h1 (show (0:ℝ)<8 by norm_num) hm.le).trans residual
      have f := (forcing_point_bound he h0 h1 (show (0:ℝ)<8 by norm_num) hm).trans forcing
      linarith) hj n
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

#print axioms ordered_bell_error_of_three_checks
#print axioms convolution_tail_bound
#print axioms residual_prefix_bound
#print axioms forcing_point_bound

end OrderedPartitions.Renewal
