import OrderedPartitions.MeanKernel

noncomputable section
open PowerSeries Finset
namespace OrderedPartitions.Kernel

private def Nonnegative (f : PowerSeries ℝ) := ∀ s, 0 ≤ coeff s f

private theorem nn_mul {f g : PowerSeries ℝ} (hf : Nonnegative f) (hg : Nonnegative g) :
    Nonnegative (f*g) := by
  intro s
  rw [coeff_mul]
  exact sum_nonneg (fun p _ ↦ mul_nonneg (hf _) (hg _))

private theorem nn_pow {f : PowerSeries ℝ} (hf : Nonnegative f) (d : ℕ) : Nonnegative (f^d) := by
  induction d with
  | zero =>
    intro s
    simp only [pow_zero, coeff_one]
    split_ifs <;> norm_num
  | succ d ih => rw [pow_succ]; exact nn_mul ih hf

private theorem mul_pos_at {f g : PowerSeries ℝ} (hf : Nonnegative f) (hg : Nonnegative g)
    {s t : ℕ} (hs : 0<coeff s f) (ht : 0<coeff t g) : 0<coeff (s+t) (f*g) := by
  rw [coeff_mul]
  exact (mul_pos hs ht).trans_le (single_le_sum (s := antidiagonal (s+t))
    (f := fun p : ℕ×ℕ ↦ coeff p.1 f * coeff p.2 g)
    (fun p _ ↦ mul_nonneg (hf _) (hg _)) (mem_antidiagonal.mpr rfl : (s,t) ∈ _))

private theorem pow_pos_at {f : PowerSeries ℝ} (hf : Nonnegative f) {s : ℕ}
    (hs : 0<coeff s f) (d : ℕ) : 0<coeff (d*s) (f^d) := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ, Nat.succ_mul]; exact mul_pos_at (nn_pow hf _) hf ih hs

private def marker (j d : ℕ) : PowerSeries ℝ := big j^(d+1) * K^d

private theorem marker_kernel (j d : ℕ) : Nonnegative (marker j d) ∧
    0<coeff ((d+1)*j) (marker j d) := by
  have rp : 0<rho := by linarith [rho_interval.1]
  have bg : Nonnegative (big j) := by intro r; rw [big_coeff]; split_ifs <;> positivity
  have kg : Nonnegative K := fun i ↦ (k_pos i).le
  have atj : 0 < coeff j (big j) := by rw [big_coeff, if_pos (le_refl _)]; positivity
  refine ⟨nn_mul (nn_pow bg _) (nn_pow kg _), ?_⟩
  simpa [marker] using mul_pos_at (nn_pow bg (d+1)) (nn_pow kg d)
    (pow_pos_at bg atj (d+1)) (pow_pos_at kg (k_pos 0) d)

private theorem marker_actual {j : ℕ} (hj : 1≤j) (d n : ℕ) :
    coeff n (marker j d*K^2) = (2*rho)^(d+2) * (rho^n/n.factorial) * markedCount n j (d+1) := by
  have id : marker j d*K^2 = C ((2*rho)^(d+2))*rescale rho (momentSeries j (d+1)) := by
    rw [marked_segments hj, free_series hj]
    simp only [marker, big, K, Renewal.scaledH, map_mul, map_pow, mul_pow]
    ring
  rw [id, coeff_C_mul, coeff_rescale]
  simp only [momentSeries, coeff_mk]
  ring

/-- At every positive order the actual binomial moment increases strictly once that
order is present. Here the uniform sample space consists of all ordered partitions. -/
theorem original_binomial_moment_strict {j n : ℕ} (hj : 2≤j) (d : ℕ)
    (hn : (d+1)*j ≤ n) :
    markedCount n j (d+1) / (row n j).eval 1 <
      markedCount (n+1) j (d+1) / (row (n+1) j).eval 1 := by
  obtain ⟨non,pos⟩ := marker_kernel j d
  have n2 : 2≤n := by nlinarith
  have rp : 0<rho := by linarith [rho_interval.1]
  have j1 : 1≤j := by omega
  have det := lt_trans (mul_pos (show (0:ℝ)<2/5 by norm_num) pos)
    (convolution_barrier n2 hn _ non pos)
  rw [k_row j1, k_row j1, marker_actual j1, marker_actual j1, sub_pos] at det
  apply (div_lt_div_iff₀ (original_eval_pos j1 _) (original_eval_pos j1 _)).mpr
  let u := (2*rho)^(d+2)*(2*rho)*(rho^n/n.factorial)*(rho^(n+1)/(n+1).factorial)
  have hup : 0<u := by dsimp [u]; positivity
  apply lt_of_mul_lt_mul_left (a:=u) _ hup.le
  dsimp [u]
  linarith only [det]

theorem markedCount_before {j h n : ℕ} (hj : 1≤j) (hn : n<h*j) :
    markedCount n j h = 0 := by
  rw [markedCount_eq_count]
  apply sum_eq_zero
  intro d _
  by_cases hd : d<h
  · rw [Nat.choose_eq_zero_of_lt hd]; simp
  · have hh := hn.trans_le (Nat.mul_le_mul_right j (by omega : h≤d))
    rw [count_above_degree hj hh]; simp

theorem markedCount_starts {j : ℕ} (hj : 1≤j) (d : ℕ) :
    0<markedCount ((d+1)*j) j (d+1) := by
  obtain ⟨non,pos⟩ := marker_kernel j d
  have kg : Nonnegative K := fun n ↦ (k_pos _).le
  have kw : 0<coeff 0 (K^2) := by simpa using pow_pos_at kg (k_pos 0) 2
  have m := mul_pos_at non (nn_pow kg 2) pos kw
  rw [Nat.add_zero, marker_actual hj] at m
  have rp : 0<rho := by linarith [rho_interval.1]
  exact pos_of_mul_pos_right m (by positivity)

/-- Includes the jump from zero at the rank immediately preceding the first occurrence. -/
theorem original_binomial_moment_from_entry {j n : ℕ} (hj : 2≤j) (d : ℕ)
    (hn : (d+1)*j ≤ n+1) :
    markedCount n j (d+1) / (row n j).eval 1 <
      markedCount (n+1) j (d+1) / (row (n+1) j).eval 1 := by
  by_cases h : (d+1)*j ≤ n
  · exact original_binomial_moment_strict hj d h
  · have j1 : 1≤j := by omega
    have e : n+1=(d+1)*j := by omega
    rw [markedCount_before j1 (by omega), zero_div, e]
    exact div_pos (markedCount_starts j1 d) (original_eval_pos j1 _)

#print axioms original_binomial_moment_from_entry
#print axioms original_binomial_moment_strict
end OrderedPartitions.Kernel
