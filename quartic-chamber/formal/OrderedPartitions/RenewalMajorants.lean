import OrderedPartitions.RenewalTails

noncomputable section
open Finset PowerSeries
namespace OrderedPartitions.Renewal

theorem q_step (rho : ℝ) (n : ℕ) :
    q rho (n+1) = q rho n * (rho/(n+1)) := by
  simp only [q, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem q_half {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho ≤ 1) {m : ℕ} (hm : 1 ≤ m) (i : ℕ) :
    q rho (i+m) ≤ (1/2 : ℝ)^i * q rho m := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hratio : rho/((i+m : ℕ)+1) ≤ (1/2 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hi : (1:ℝ) ≤ ((i+m:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ i+m)
      linarith
    rw [show i+1+m=i+m+1 by omega, q_step, pow_succ]
    calc
      _ ≤ ((1/2:ℝ)^i * q rho m)*(1/2) := mul_le_mul ih hratio (by positivity)
        (by unfold q; positivity)
      _ = _ := by ring

theorem q_tail_upper {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    (∑' i, q rho (i+m)) ≤ 2*q rho m := by
  have hs := (summable_nat_add_iff m).mpr (q_hasSum rho).summable
  have hg := (hasSum_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
    (by norm_num)).mul_right (q rho m)
  rw [← show (1-(1/2:ℝ))⁻¹ * q rho m = 2*q rho m by norm_num, ← hg.tsum_eq]
  exact hs.tsum_le_tsum (q_half h0 h1 hm) hg.summable

theorem factorB_bounds {rho : ℝ} (he : Real.exp rho = 2) (h0 : 0 ≤ rho) (h1 : rho ≤ 1)
    (n : ℕ) : 0 ≤ coeff n (factorB rho) ∧ coeff n (factorB rho) ≤ 2*q rho (n+1) := by
  rw [factorB_tail he]
  exact ⟨tsum_nonneg (fun _ ↦ by unfold q; positivity), q_tail_upper h0 h1 (by omega)⟩

theorem forcingJ_bounds {rho : ℝ} (he : Real.exp rho = 2) (h0 : 0 ≤ rho) (h1 : rho ≤ 1)
    (n : ℕ) : 0 ≤ coeff n (forcingJ rho) ∧ coeff n (forcingJ rho) ≤ 4*q rho (n+2) := by
  rw [forcingJ_tail he h0]
  refine ⟨tsum_nonneg (fun _ ↦ (factorB_bounds he h0 h1 _).1), ?_⟩
  have hs := (summable_nat_add_iff (n+1)).mpr (b_hasSum he h0).summable
  have hq := (summable_nat_add_iff (n+2)).mpr (q_hasSum rho).summable
  calc
    _ ≤ ∑' i, 2*q rho (i+(n+2)) := hs.tsum_le_tsum (fun i ↦ by
      simpa [Nat.add_assoc] using (factorB_bounds he h0 h1 (i+(n+1))).2) (hq.mul_left 2)
    _ = 2*(∑' i, q rho (i+(n+2))) := hq.tsum_mul_left 2
    _ ≤ 4*q rho (n+2) := by linarith [q_tail_upper h0 h1 (m := n+2) (by omega)]

theorem t_zero (rho : ℝ) (N : ℕ) : coeff 0 (seriesT rho N)=1 := by
  rw [seriesT_coeff, if_pos (Nat.zero_le _), sub_mul, one_mul, map_sub,
    scaledH_coeff rho (j := 1) (by omega)]
  simp [row_zero (by omega : 1 ≤ 1)]

theorem t_succ (rho : ℝ) {i N : ℕ} (hi : i+1 ≤ N) {j : ℕ} (hj : 1 ≤ j) :
    coeff (i+1) (seriesT rho N) =
      rho^i * (rho*(row (i+1) j).eval 1 - (i+1)*(row i j).eval 1)/(i+1).factorial := by
  rw [seriesT_coeff, if_pos hi, sub_mul, one_mul, map_sub, coeff_succ_X_mul,
    scaledH_coeff rho hj, scaledH_coeff rho hj, pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- Only terms through the inclusive degree bound contribute to this coefficient. -/
theorem truncated_product_coeff (rho : ℝ) {N n : ℕ} (hn : N ≤ n) (S : PowerSeries ℝ) :
    coeff n (seriesT rho N * S) =
    ∑ i ∈ range (N+1), coeff i (seriesT rho N) * coeff (n-i) S := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  apply sum_subset (range_mono (by omega))
  intro i _ hi
  rw [seriesT_coeff, if_neg (by simpa using hi), zero_mul]

theorem residualP_late (rho : ℝ) {N n : ℕ} (hn : N < n) : coeff n (residualP rho N) =
    -(∑ i ∈ range (N+1), coeff i (seriesT rho N) * coeff (n-i) (factorB rho)) := by
  rw [residualP, map_sub, coeff_one, if_neg (by omega), zero_sub, truncated_product_coeff rho hn.le]

#print axioms q_tail_upper
#print axioms factorB_bounds
#print axioms forcingJ_bounds
#print axioms t_zero
#print axioms t_succ
#print axioms truncated_product_coeff
#print axioms residualP_late

end OrderedPartitions.Renewal
