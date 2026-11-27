import OrderedPartitions.RenewalKernelBounds

noncomputable section
open PowerSeries Finset
namespace OrderedPartitions.Kernel

theorem k_pos (n : ℕ) : 0 < coeff n K := by
  have h := (eps_bound n).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0:ℝ)<2)
    (show (2:ℝ)≤2*8^n by linarith [one_le_pow₀ (show (1:ℝ)≤8 by norm_num) (n:=n)]))
  unfold eps at h
  have := (abs_le.mp h).1
  linarith

private theorem small_factor {n : ℕ} (hn : 2 ≤ n) : ((n:ℝ)+3)/8^n ≤ 5/64 := by
  apply (div_le_iff₀ (by positivity)).mpr
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
    rw [pow_succ]; push_cast
    linarith [one_le_pow₀ (show (1:ℝ)≤8 by norm_num) (n:=n), Nat.cast_nonneg (α:=ℝ) n]

theorem kernel_barrier {n s : ℕ} (hn : 2≤n) (hs : s≤n) :
    2/5 < coeff n K * g (s+1) - coeff (n+1) K * g s := by
  have hpow : (64:ℝ) ≤ 8^n := by
    calc
      (64:ℝ) = 8^(2:ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn
  have e := eps_bound n
  have e' := eps_bound (n+1)
  have en := abs_le.mp e
  have en' := abs_le.mp e'
  have eb : (1:ℝ)/(2*8^n) ≤ 1/128 :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith : (128:ℝ) ≤ 2*8^n))
  have kc : (127:ℝ)/128 ≤ coeff n K := by unfold eps at en; linarith [en.1]
  have dg := abs_le.mp (g_increment_error s)
  have damp : (525/1000:ℝ)/4^s ≤ 525/1000 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  have dg' : (19:ℝ)/40 ≤ g (s+1)-g s := by linarith [dg.1]
  have dk : coeff (n+1) K - coeff n K ≤ (9/16:ℝ)/8^n := by
    unfold eps at en en'
    rw [pow_succ] at en'
    have h : (1:ℝ)/(2*8^n)+1/(2*(8^n*8)) = (9/16:ℝ)/8^n := by field_simp; ring
    linarith [en.1,en'.2]
  have gu := (g_bounds s).2
  have gl := (g_bounds s).1
  have gle : g s ≤ (n:ℝ)+3 := by linarith [show (s:ℝ)≤n by exact_mod_cast hs]
  have err := mul_le_mul dk gle (show 0≤g s by linarith) (by positivity)
  have sc := small_factor hn
  have hsc : ((9/16:ℝ)/8^n)*((n:ℝ)+3) ≤ (9/16)*(5/64) := by
    calc
      _ = (9/16:ℝ)*(((n:ℝ)+3)/8^n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left sc (by norm_num)
  have m := mul_le_mul kc dg' (by norm_num) (le_of_lt (k_pos n))
  nlinarith [err.trans hsc]


/-- A nonnegative marker can be inserted in the middle free-list kernel. -/
theorem convolution_barrier {n r₀ : ℕ} (hn : 2≤n) (hr : r₀≤n) (V : PowerSeries ℝ)
    (hv : ∀ r, 0 ≤ coeff r V) (vpos : 0 < coeff r₀ V) :
    (2/5)*coeff r₀ V <
    coeff n K * coeff (n+1) (V*K^2) - coeff (n+1) K * coeff n (V*K^2) := by
  have expand (N : ℕ) : coeff N (V*K^2) = ∑ r ∈ range (N+1), coeff r V*g (N-r) := by
    rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rfl
  rw [expand, expand, sum_range_succ (fun r ↦ coeff r V*g (n+1-r)), mul_add, mul_sum, mul_sum]
  have core : (2/5)*coeff r₀ V <
      ∑ r ∈ range (n+1), (coeff n K*(coeff r V*g (n+1-r)) -
        coeff (n+1) K*(coeff r V*g (n-r))) := by
    have step (r : ℕ) (h : r ≤ n) :
        coeff n K*(coeff r V*g (n+1-r)) - coeff (n+1) K*(coeff r V*g (n-r)) =
        coeff r V*(coeff n K*g ((n-r)+1) - coeff (n+1) K*g (n-r)) := by
      rw [show n+1-r=n-r+1 by omega]; ring
    have hmain := mul_lt_mul_of_pos_left (kernel_barrier hn (s:=n-r₀) (by omega)) vpos
    have single := single_le_sum (f := fun r ↦ coeff n K*(coeff r V*g (n+1-r)) -
        coeff (n+1) K*(coeff r V*g (n-r))) (s := range (n+1)) (fun r h ↦ by
          rw [step r (Nat.le_of_lt_succ (mem_range.mp h))]
          exact mul_nonneg (hv r) (le_of_lt (lt_trans (by norm_num) (kernel_barrier hn (by omega)))))
        (mem_range.mpr (Nat.lt_succ_of_le hr))
    rw [step r₀ hr] at single
    linarith
  rw [sum_sub_distrib] at core
  simp only [Nat.sub_self]
  have gg := (g_bounds 0).1
  have extra := mul_nonneg (k_pos n).le (mul_nonneg (hv (n+1)) (show 0≤g 0 by linarith))
  linarith

def big (j : ℕ) : PowerSeries ℝ := rescale rho (sizeSeries j)

theorem big_coeff (j n : ℕ) : coeff n (big j) =
    if j≤n then rho^n/n.factorial else 0 := by
  rw [big, coeff_rescale, sizeSeries, coeff_mk]
  split_ifs <;> simp [div_eq_mul_inv]

theorem k_row {j : ℕ} (hj : 1≤j) (n : ℕ) :
    coeff n K = (2*rho)*(rho^n/n.factorial)*(row n j).eval 1 := by
  rw [K, coeff_C_mul, Renewal.scaledH_coeff rho hj]
  ring

theorem g_marked {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    coeff n (big j*K^2) = (2*rho)^2 * (rho^n/n.factorial) * (row n j).derivative.eval 1 := by
  have heq : big j*K^2 = C ((2*rho)^2)*rescale rho (momentSeries j 1) := by
    simp only [big,K,Renewal.scaledH, marked_segments hj 1, pow_one, free_series hj,
      map_mul, map_pow]
    ring
  rw [heq, coeff_C_mul, coeff_rescale]
  simp only [momentSeries, coeff_mk, markedCount_one]
  ring

theorem original_eval_pos {j : ℕ} (hj : 1≤j) (n : ℕ) : 0 < (row n j).eval 1 := by
  have h := k_pos n
  rw [k_row hj] at h
  have rp : 0<rho := by linarith [rho_interval.1]
  exact pos_of_mul_pos_right h (by positivity)

theorem original_mean_strict {j n : ℕ} (hj : 2 ≤ j) (hn : j ≤ n) :
    (row n j).derivative.eval 1 / (row n j).eval 1 <
      (row (n+1) j).derivative.eval 1 / (row (n+1) j).eval 1 := by
  have rp : 0<rho := by linarith [rho_interval.1]
  have non (r : ℕ) : 0 ≤ coeff r (big j) := by rw [big_coeff]; split_ifs <;> positivity
  have pos : 0 < coeff j (big j) := by rw [big_coeff, if_pos (le_refl _)]; positivity
  have h := convolution_barrier (hj.trans hn) hn (big j) non pos
  have j1 : 1 ≤ j := by omega
  have gt := lt_trans (mul_pos (show (0:ℝ) < 2/5 by norm_num) pos) h
  rw [k_row j1, k_row j1, g_marked j1, g_marked j1, sub_pos] at gt
  apply (div_lt_div_iff₀ (original_eval_pos j1 _) (original_eval_pos j1 _)).mpr
  have common : 0 < (2*rho)^3*(rho^n/n.factorial)*(rho^(n+1)/(n+1).factorial) := by positivity
  apply lt_of_mul_lt_mul_left (a := (2*rho)^3*(rho^n/n.factorial)*(rho^(n+1)/(n+1).factorial)) _ common.le
  linarith only [gt]

#print axioms kernel_barrier
#print axioms convolution_barrier
#print axioms original_mean_strict
end OrderedPartitions.Kernel
