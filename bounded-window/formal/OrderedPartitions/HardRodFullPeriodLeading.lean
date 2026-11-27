import OrderedPartitions.HardRodEntryGrowth

/-! A uniform comparison for two actual normalized coefficients one full period apart. -/
noncomputable section
namespace OrderedPartitions.Kernel
open Finset PowerSeries

private theorem bell_bounds (s : ℕ) : 1/2 ≤ coeff s K ∧ coeff s K ≤ 3/2 := by
  have he := abs_le.mp (eps_bound s)
  have hpow := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 8) (n := s)
  have small : 1/(2*8^(s:ℕ)) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  unfold eps at he
  constructor <;> linarith

private theorem prod_expansion (V W : PowerSeries ℝ) (m : ℕ) :
    coeff m (V*W) = ∑ i ∈ range (m+1), coeff i V * coeff (m-i) W := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem nonneg_mul {V W : PowerSeries ℝ} (v : ∀ i, 0 ≤ coeff i V)
    (w : ∀ i, 0 ≤ coeff i W) (i : ℕ) : 0 ≤ coeff i (V*W) := by
  rw [prod_expansion]
  exact sum_nonneg fun a _ ↦ mul_nonneg (v a) (w _)

private theorem nonneg_pow {V : PowerSeries ℝ} (v : ∀ i, 0 ≤ coeff i V)
    (a i : ℕ) : 0 ≤ coeff i (V^a) := by
  induction a generalizing i with
  | zero => simp [coeff_one, apply_ite]
  | succ a ih => rw [pow_succ]; exact nonneg_mul ih v i

private theorem coeff_comparison {W : PowerSeries ℝ} (nonneg : ∀ i, 0 ≤ coeff i W)
    {s m : ℕ} (h : s ≤ m) : coeff s (W*K) ≤ 3*coeff m (W*K) := by
  simp only [prod_expansion, mul_sum]
  calc
    _ ≤ ∑ i ∈ range (s+1), 3 * (coeff i W * coeff (m-i) K) := by
      apply sum_le_sum
      intro i _
      have bound : coeff (s-i) K ≤ 3*coeff (m-i) K := by
        linarith [(bell_bounds (s-i)).2,(bell_bounds (m-i)).1]
      calc
        _ ≤ coeff i W * (3*coeff (m-i) K) := mul_le_mul_of_nonneg_left bound (nonneg i)
        _ = _ := by ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      (fun i _ _ ↦ by positivity [nonneg i, (k_pos (m-i)).le])

private theorem next_kernel_bound {j : ℕ} (hj : 50 ≤ j) (s : ℕ) :
    coeff s (markerB j*K) ≤ 2 := by
  rw [prod_expansion]
  calc
    _ ≤ ∑ i ∈ range (s+1), coeff i (markerB j)*(3/2) :=
      sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (bell_bounds _).2 (marker_positive j i).le)
    _ ≤ 2 := by rw [← sum_mul]; linarith [marker_partial hj (s+1)]

theorem full_period_kernel_bound {j : ℕ} (hj : 50 ≤ j) (d m : ℕ) :
    coeff m (markerB j^(d+1)*K^(d+2)) ≤
      6*((m:ℝ)+1)*coeff m (markerB j^d*K^(d+1)) := by
  let W := markerB j^d*K^d
  have wn (s : ℕ) : 0 ≤ coeff s W :=
    nonneg_mul (nonneg_pow (fun i ↦ (marker_positive j i).le) d)
      (nonneg_pow (fun i ↦ (k_pos i).le) d) s
  have wkn (s : ℕ) := nonneg_mul wn (fun i ↦ (k_pos i).le) s
  have old : markerB j^d*K^(d+1) = W*K := by dsimp [W]; ring
  have new : markerB j^(d+1)*K^(d+2) = (W*K)*(markerB j*K) := by dsimp [W]; ring
  rw [old,new,prod_expansion]
  calc
    _ ≤ ∑ i ∈ range (m+1), 6 * coeff m (W*K) := by
      apply sum_le_sum
      intro i hi
      have h := coeff_comparison wn (show i ≤ m by have := mem_range.mp hi; omega)
      have b := next_kernel_bound hj (m-i)
      calc
        _ ≤ coeff i (W*K) * 2 := mul_le_mul_of_nonneg_left b (wkn i)
        _ ≤ 6 * coeff m (W*K) := by linarith
    _ = _ := by simp; ring

/-- At the same excess m, moving up one marked degree and one full period in
the original rank costs at most 18 (m+1)/j, uniformly in that degree. -/
theorem full_period_leading_bound {j : ℕ} (hj : 50 ≤ j) (d m : ℕ) :
    (j:ℝ) * windowCoeff j (m+(d+1)*j) (d+1) ≤
      18*((m:ℝ)+1)*windowCoeff j (m+d*j) d := by
  have jp : 0 < (j:ℝ) := by exact_mod_cast (show 0<j by omega)
  simp only [windowCoeff, normalizedMoment_coeff (by omega : 1 ≤ j),pow_succ (j:ℝ)]
  have n0 := k_pos (m+d*j)
  have n1 := k_pos (m+(d+1)*j)
  have no : 0 ≤ coeff m (markerB j^d*K^(d+1)) :=
    nonneg_mul (nonneg_pow (fun i ↦ (marker_positive j i).le) d)
      (nonneg_pow (fun i ↦ (k_pos i).le) (d+1)) m
  have cmp : coeff (m+d*j) K ≤ 3 * coeff (m+(d+1)*j) K := by
    linarith [(bell_bounds (m+d*j)).2,(bell_bounds (m+(d+1)*j)).1]
  have scale : 0 ≤ 6*((m:ℝ)+1)*coeff m (markerB j^d*K^(d+1)) := by positivity
  have rel := mul_le_mul (full_period_kernel_bound hj d m) cmp n0.le scale
  field_simp [n0.ne',n1.ne',jp.ne']
  nlinarith only [rel]

#print axioms full_period_kernel_bound
#print axioms full_period_leading_bound
end OrderedPartitions.Kernel
