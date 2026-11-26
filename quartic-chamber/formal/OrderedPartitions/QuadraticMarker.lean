import OrderedPartitions.MeanKernel

noncomputable section
open PowerSeries Finset
namespace OrderedPartitions.Kernel

def markScale (j : ℕ) : ℝ := (rho^j/j.factorial)/(2*rho)
def markerB (j : ℕ) : PowerSeries ℝ := PowerSeries.mk fun i ↦
  rho^i*(j.factorial:ℝ)/(j+i).factorial

theorem marker_zero (j : ℕ) : coeff 0 (markerB j) = 1 := by simp [markerB, Nat.factorial_ne_zero]

theorem marker_step (j i : ℕ) : coeff (i+1) (markerB j) =
    coeff i (markerB j)*rho/(j+i+1) := by
  simp only [markerB, coeff_mk, ← Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem marker_positive (j i : ℕ) : 0 < coeff i (markerB j) := by
  have hr : 0<rho := by linarith [rho_interval.1]
  simp only [markerB, coeff_mk]
  positivity

theorem shifted_marker (j : ℕ) :
    big j = C (rho^j/j.factorial)*(X^j*markerB j) := by
  ext n
  rw [big_coeff, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with h
  · obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_sub_cancel_left,markerB,coeff_mk,pow_add]
    field_simp
  · simp

def normalizedMoment (n j h : ℕ) : ℝ :=
  markedCount n j h / (row n j).eval 1 / markScale j ^ h

theorem normalizedMoment_coeff {j : ℕ} (hj : 1≤j) (h s : ℕ) :
    normalizedMoment (s+h*j) j h =
      coeff s (markerB j^h*K^(h+1)) / coeff (s+h*j) K := by
  let n := s+h*j
  have eqn : big j^h*K^(h+1) = C ((2*rho)^(h+1))*rescale rho (momentSeries j h) := by
    rw [marked_segments hj, free_series hj]
    simp only [big, K, Renewal.scaledH, map_mul, map_pow, mul_pow]
    ring
  have shift : big j^h*K^(h+1) =
      C ((rho^j/j.factorial)^h)*(X^(h*j)*(markerB j^h*K^(h+1))) := by
    rw [shifted_marker]
    simp only [mul_pow, ← map_pow, ← pow_mul, mul_comm j h]
    ring
  have raw := congrArg (coeff n) (shift.symm.trans eqn)
  simp only [coeff_C_mul, n, coeff_X_pow_mul, coeff_rescale, momentSeries, coeff_mk] at raw
  have rp : 0 < rho := by linarith [rho_interval.1]
  rw [normalizedMoment, k_row hj, markScale]
  have ev := original_eval_pos hj (s+h*j)
  have fac : (0:ℝ) < (s+h*j).factorial := by positivity
  rw [div_pow, div_pow] at *
  field_simp at raw ⊢
  rw [pow_succ (2*rho) h] at raw
  nlinarith only [raw]

def markerRatio : ℝ := 7/510

theorem marker_envelope {j : ℕ} (hj : 50≤j) (i : ℕ) :
    coeff i (markerB j) ≤ markerRatio^i := by
  have hr : 0<rho := by linarith [rho_interval.1]
  induction i with
  | zero => simp [marker_zero]
  | succ i ih =>
    rw [marker_step, pow_succ]
    have ratio : rho/(j+i+1) ≤ markerRatio := by
      have jj : (50:ℝ) ≤ j := by exact_mod_cast hj
      apply (div_le_iff₀ (by positivity)).mpr
      unfold markerRatio
      linarith [rho_interval.2, Nat.cast_nonneg (α:=ℝ) i]
    rw [mul_div_assoc]
    exact mul_le_mul ih ratio (by positivity) (by unfold markerRatio; positivity)

theorem marker_partial {j : ℕ} (hj : 50≤j) (N : ℕ) :
    ∑ i ∈ range N, coeff i (markerB j) ≤ 1014/1000 := by
  apply (sum_le_sum (fun i _ ↦ marker_envelope hj i)).trans
  have g := geom_sum_mul (markerRatio) N
  have pos : 0 ≤ markerRatio^N := by unfold markerRatio; positivity
  unfold markerRatio at *
  linarith

theorem marker_square_partial {j : ℕ} (hj : 50≤j) (N : ℕ) :
    ∑ i ∈ range N, coeff i (markerB j^2) ≤ 1029/1000 := by
  let b := fun i ↦ coeff i (markerB j)
  have expand (i : ℕ) : coeff i (markerB j^2) = ∑ t ∈ range (i+1), b t*b (i-t) := by
    rw [pow_two,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [expand]
  rw [sum_range_diag_flip N (fun a c ↦ b a*b c)]
  simp_rw [← mul_sum]
  calc
    _ ≤ ∑ i ∈ range N, b i*(1014/1000) := by
      exact sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (marker_partial hj _) (marker_positive j i).le)
    _ = (∑ i ∈ range N, b i)*(1014/1000) := (sum_mul ..).symm
    _ ≤ (1014/1000:ℝ)*(1014/1000) :=
      mul_le_mul_of_nonneg_right (marker_partial hj _) (by norm_num)
    _ ≤ _ := by norm_num

#print axioms marker_square_partial
#print axioms shifted_marker
#print axioms normalizedMoment_coeff
#print axioms marker_partial
end OrderedPartitions.Kernel
