import OrderedPartitions.RenewalConvolution

noncomputable section
open Finset
namespace OrderedPartitions.Renewal

private theorem tail_ratio_half {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : 2*a ≤ (m:ℝ)+1) (i : ℕ) :
    q a (i+m) ≤ (1/2:ℝ)^i*q a m := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show i+1+m=i+m+1 by omega, q_step, pow_succ]
    have h : a / ((i+m : ℕ)+1) ≤ (1/2:ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    calc
      _ ≤ ((1/2:ℝ)^i*q a m)*(1/2) := mul_le_mul ih h (by positivity) (by unfold q; positivity)
      _ = _ := by ring

theorem expTail_truncate {a : ℝ} (ha : 0 ≤ a) (lo L : ℕ)
    (h : 2*a ≤ ((lo+L:ℕ):ℝ)+1) :
    expTail a lo ≤ (∑ i ∈ range L, q a (i+lo)) + 2*q a (lo+L) := by
  have hs := (summable_nat_add_iff lo).mpr (q_hasSum a).summable
  have split := hs.sum_add_tsum_nat_add L
  change (∑' i, q a (i+lo)) ≤ _
  rw [← split]
  apply add_le_add_right
  have hg := (hasSum_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
      (by norm_num)).mul_right (q a (lo+L))
  rw [← show (1-(1/2:ℝ))⁻¹*q a (lo+L)=2*q a (lo+L) by norm_num, ← hg.tsum_eq]
  apply ((summable_nat_add_iff L).mpr hs).tsum_le_tsum _ hg.summable
  intro i
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using tail_ratio_half ha h i

theorem expTail_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (lo : ℕ) :
    expTail a lo ≤ expTail b lo := by
  apply ((summable_nat_add_iff lo).mpr (q_hasSum a).summable).tsum_le_tsum _
    ((summable_nat_add_iff lo).mpr (q_hasSum b).summable)
  intro i
  unfold q
  gcongr

/-- Replace the true exponential tail by a finite rational expression at any rational majorant. -/
theorem expTail_finite_majorant {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {lo endIndex : ℕ} (hle : lo ≤ endIndex+1) (hh : 2*b ≤ (endIndex:ℝ)+2) :
    expTail a lo ≤ (∑ i ∈ range (endIndex+1-lo), q b (i+lo)) + 2*q b (endIndex+1) := by
  have sum : lo+(endIndex+1-lo)=endIndex+1 := by omega
  have hr : 2*b ≤ ((lo+(endIndex+1-lo):ℕ):ℝ)+1 := by rw [sum]; push_cast; linarith
  simpa only [sum] using (expTail_mono ha hab lo).trans
    (expTail_truncate (ha.trans hab) lo (endIndex+1-lo) hr)

/-- The finite scalar sum uses any upper bounds on the retained absolute taps and
on the rescaled exponential parameter. Both can thus be replaced by rational intervals. -/
theorem tailCost_le_finite {rho R c a : ℝ} (h0 : 0 ≤ rho) (hr : 0 < R) (hc : 0 ≤ c)
    (ha : R*rho ≤ a) (N d endIndex : ℕ) (hh : 2*a ≤ (endIndex:ℝ)+2)
    (hsize : N+d ≤ endIndex) (w : ℕ → ℝ)
    (hw : ∀ i ≤ N, |PowerSeries.coeff i (seriesT rho N)| * R^i ≤ w i) :
    tailCost rho R c N d ≤ ∑ i ∈ range (N+1), w i * (c/R^d *
      ((∑ u ∈ range (endIndex+1-(N+1-i+d)), q a (u+(N+1-i+d))) + 2*q a (endIndex+1))) := by
  apply sum_le_sum
  intro i hi
  have hiN := Nat.le_of_lt_succ (mem_range.mp hi)
  have H := expTail_finite_majorant (mul_nonneg hr.le h0) ha
    (lo := N+1-i+d) (endIndex := endIndex) (by omega) hh
  have ht : 0 ≤ expTail (R*rho) (N+1-i+d) := tsum_nonneg (fun k ↦ by unfold q; positivity)
  have hw0 : 0 ≤ w i := (show 0 ≤ |PowerSeries.coeff i (seriesT rho N)| * R^i by positivity).trans (hw i hiN)
  exact mul_le_mul (hw i hiN) (mul_le_mul_of_nonneg_left H (by positivity)) (by positivity) hw0

#print axioms tailCost_le_finite
#print axioms expTail_truncate
#print axioms expTail_mono
#print axioms expTail_finite_majorant
end OrderedPartitions.Renewal
