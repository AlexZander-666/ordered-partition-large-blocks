import OrderedPartitions.QuadraticMarker

/-! A relative increment bound for the normalized marked counts at entry. -/

noncomputable section
open Finset PowerSeries

namespace OrderedPartitions.Kernel

private theorem k_le_three_halves (n : ℕ) : coeff n K ≤ 3/2 := by
  have eb := (abs_le.mp (eps_bound n)).2
  have b := div_le_self (by norm_num : (0:ℝ) ≤ 1/2)
    (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 8) (n := n))
  unfold eps at eb
  rw [div_mul_eq_div_div] at eb
  linarith

/-- A positive convolution preserves the relative increase after division by
the two actual ordered Bell normalizers. -/
theorem convolution_relative_growth {n m : ℕ} (hn : 2 ≤ n) (hm : m ≤ n)
    (V : PowerSeries ℝ) (nonneg : ∀ i, 0 ≤ coeff i V) :
    coeff m (V*K^2) / coeff n K ≤ 4*((m:ℝ)+3) *
      (coeff (m+1) (V*K^2) / coeff (n+1) K - coeff m (V*K^2) / coeff n K) := by
  let U := fun s ↦ coeff s (V*K^2)
  let mass := ∑ r ∈ range (m+1), coeff r V
  have mass_nonneg : 0 ≤ mass := sum_nonneg (fun r _ ↦ nonneg r)
  have expand (s : ℕ) : U s = ∑ r ∈ range (s+1), coeff r V*g (s-r) := by
    change coeff s (V*K^2) = _
    rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rfl
  have upper : U m ≤ ((m:ℝ)+3)*mass := by
    rw [expand]
    dsimp only [mass]
    rw [mul_sum]
    refine sum_le_sum (fun r _ ↦ ?_)
    rw [mul_comm ((m:ℝ)+3)]
    apply mul_le_mul_of_nonneg_left _ (nonneg r)
    have suble : ((m-r:ℕ):ℝ) ≤ m := by exact_mod_cast Nat.sub_le m r
    linarith [(g_bounds (m-r)).2]
  have un : 0 ≤ U m := by
    rw [expand]
    refine sum_nonneg (fun r _ ↦ mul_nonneg (nonneg r) ?_)
    linarith [(g_bounds (m-r)).1, Nat.cast_nonneg (α := ℝ) (m-r)]
  have det : (2/5:ℝ)*mass ≤ coeff n K*U (m+1)-coeff (n+1) K*U m := by
    rw [expand m, expand (m+1), sum_range_succ (fun r ↦ coeff r V*g (m+1-r)), mul_add]
    have each :
        (2/5:ℝ)*mass ≤ ∑ r ∈ range (m+1),
        (coeff n K*(coeff r V*g (m+1-r))-coeff (n+1) K*(coeff r V*g (m-r))) := by
      dsimp only [mass]
      rw [mul_sum]
      refine sum_le_sum (fun r hr ↦ ?_)
      have hrel : m+1-r=(m-r)+1 := by have := mem_range.mp hr; omega
      rw [hrel]
      calc
        _ ≤ coeff r V*(coeff n K*g ((m-r)+1)-coeff (n+1) K*g (m-r)) := by
          rw [mul_comm (2/5:ℝ)]
          exact mul_le_mul_of_nonneg_left (kernel_barrier hn (by omega : m-r ≤ n)).le (nonneg r)
        _ = _ := by ring
    rw [sum_sub_distrib] at each
    simp only [mul_sum] at each ⊢
    have g0 : 0 ≤ g (m+1-(m+1)) := by
      simp only [Nat.sub_self]
      linarith [(g_bounds 0).1]
    have endterm := mul_nonneg (k_pos n).le (mul_nonneg (nonneg (m+1)) g0)
    linarith only [each, endterm]
  have scale : 0 ≤ (m:ℝ)+3 := by positivity
  have bound :
      coeff (n+1) K*U m ≤ 4*((m:ℝ)+3)*(coeff n K*U (m+1)-coeff (n+1) K*U m) := by
    calc
      _ ≤ (3/2:ℝ)*U m := mul_le_mul_of_nonneg_right (k_le_three_halves _) un
      _ ≤ (3/2:ℝ)*(((m:ℝ)+3)*mass) := mul_le_mul_of_nonneg_left upper (by norm_num)
      _ ≤ (8/5:ℝ)*(((m:ℝ)+3)*mass) :=
        mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg scale mass_nonneg)
      _ = 4*((m:ℝ)+3)*((2/5:ℝ)*mass) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left det (by positivity)
  change U m / coeff n K ≤ 4*((m:ℝ)+3) * (U (m+1) / coeff (n+1) K - U m / coeff n K)
  have left : U m / coeff n K = coeff (n+1) K*U m / (coeff n K*coeff (n+1) K) := by
    field_simp [(k_pos n).ne', (k_pos (n+1)).ne']
  have right : U (m+1) / coeff (n+1) K - U m / coeff n K =
      (coeff n K*U (m+1)-coeff (n+1) K*U m) / (coeff n K*coeff (n+1) K) := by
    field_simp [(k_pos n).ne', (k_pos (n+1)).ne']
  rw [right, left, ← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right (mul_pos (k_pos n) (k_pos (n+1)))).mpr bound

private theorem coeff_nonnegative_mul {F G : PowerSeries ℝ}
    (f : ∀ i, 0 ≤ coeff i F) (g : ∀ i, 0 ≤ coeff i G) (i : ℕ) :
    0 ≤ coeff i (F*G) := by
  rw [coeff_mul]
  exact sum_nonneg (fun r _ ↦ mul_nonneg (f r.1) (g r.2))

private theorem coeff_nonnegative_pow {F : PowerSeries ℝ} (f : ∀ i, 0 ≤ coeff i F)
    (d i : ℕ) : 0 ≤ coeff i (F^d) := by
  induction d generalizing i with
  | zero => simp [coeff_one, apply_ite]
  | succ d ih => rw [pow_succ]; exact coeff_nonnegative_mul ih f i

/-- The bound is uniform in the marking order and includes the first rank.
The hard-rod variable multiplies both moments by the same positive factor. -/
theorem normalizedMoment_relative_growth {j h : ℕ} (hj : 2 ≤ j) (hh : 1 ≤ h) (m : ℕ) :
    normalizedMoment (m+h*j) j h ≤ 4*((m:ℝ)+3) *
      (normalizedMoment (m+h*j+1) j h - normalizedMoment (m+h*j) j h) := by
  have n2 : 2 ≤ m+h*j :=
    hj.trans ((Nat.le_mul_of_pos_left j (by omega : 0<h)).trans (Nat.le_add_left _ _))
  let V := markerB j^h*K^(h-1)
  have nonneg (i : ℕ) : 0 ≤ coeff i V :=
    coeff_nonnegative_mul (coeff_nonnegative_pow (fun i ↦ (marker_positive j i).le) _)
      (coeff_nonnegative_pow (fun i ↦ (k_pos i).le) _) i
  have product : V*K^2 = markerB j^h*K^(h+1) := by
    dsimp [V]
    rw [mul_assoc, ← pow_add, show h-1+2=h+1 by omega]
  have test := convolution_relative_growth n2 (Nat.le_add_right _ _) V nonneg
  have upper := normalizedMoment_coeff (by omega : 1≤j) h (m+1)
  rw [show m+1+h*j = m+h*j+1 by omega] at upper
  rw [product, ← normalizedMoment_coeff (by omega : 1≤j) h m, ← upper] at test
  exact test

#print axioms convolution_relative_growth
#print axioms normalizedMoment_relative_growth

end OrderedPartitions.Kernel
