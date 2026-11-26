import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! A finite residual certificate controls all coefficients of a scalar renewal equation. -/

namespace OrderedPartitions.Renewal
open Finset PowerSeries

/-- A polynomial or power series multiplier gives a residual equation for the same error. -/
theorem residual_identity (B E J T : PowerSeries ℝ) (h : B*E = J) :
    E = T*J + (1-T*B)*E := by rw [← h]; ring

/-- A vanishing constant coefficient makes the coefficient recurrence strictly causal. -/
theorem residual_coeff (E P D : PowerSeries ℝ) (h : E = D + P*E)
    (h₀ : coeff 0 P = 0) (n : ℕ) :
    coeff n E = coeff n D + ∑ i ∈ range n, coeff (i+1) P * coeff (n-(i+1)) E := by
  calc
    coeff n E = coeff n (D+P*E) := congrArg (coeff n) h
    _ = _ := by
      rw [map_add, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
      simp [h₀]

/-- An initial interval and a uniform absolute budget on the residual convolution
give a geometric estimate for every index. -/
theorem weighted_error (E P D : PowerSeries ℝ) (h : E = D + P*E) (h₀ : coeff 0 P = 0)
    (N : ℕ) (R M : ℝ) (hR : 0 ≤ R)
    (initial : ∀ n ≤ N, |coeff n E| * R^n ≤ M)
    (budget : ∀ n > N, |coeff n D| * R^n +
      (∑ i ∈ range n, |coeff (i+1) P| * R^(i+1)) * M ≤ M) :
    ∀ n, |coeff n E| * R^n ≤ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n ≤ N
    · exact initial n small
    have term (i : ℕ) (hi : i ∈ range n) :
        |coeff (i+1) P * coeff (n-(i+1)) E| * R^n ≤
          (|coeff (i+1) P| * R^(i+1)) * M := by
      have hil := mem_range.mp hi
      have inds : (i+1)+(n-(i+1)) = n := by omega
      have weight : R^n = R^(i+1) * R^(n-(i+1)) := by rw [← pow_add, inds]
      rw [abs_mul, weight]
      calc
        _ = (|coeff (i+1) P| * R^(i+1)) * (|coeff (n-(i+1)) E| * R^(n-(i+1))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (ih _ (by omega)) (by positivity)
    calc
      |coeff n E| * R^n ≤ (|coeff n D| +
          ∑ i ∈ range n, |coeff (i+1) P * coeff (n-(i+1)) E|) * R^n := by
        rw [residual_coeff E P D h h₀]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hR _)
        exact (abs_add_le ..).trans (add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs ..))
      _ ≤ _ := by
        rw [add_mul, sum_mul]
        apply le_trans _ (budget n (by omega))
        rw [sum_mul]
        exact add_le_add (le_refl _) (sum_le_sum term)

#print axioms residual_identity
#print axioms residual_coeff
#print axioms weighted_error
end OrderedPartitions.Renewal
