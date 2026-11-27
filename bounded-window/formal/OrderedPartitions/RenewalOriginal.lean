import OrderedPartitions.OriginalEGF
import OrderedPartitions.RenewalResidual
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Trunc

noncomputable section
open Finset PowerSeries
namespace OrderedPartitions.Renewal

def scaledH (rho : ℝ) : PowerSeries ℝ :=
  rescale rho ((2-PowerSeries.exp ℝ)⁻¹)

def geom : PowerSeries ℝ := mk 1

def factorB (rho : ℝ) : PowerSeries ℝ := (2-rescale rho (PowerSeries.exp ℝ))*geom
def forcingJ (rho : ℝ) : PowerSeries ℝ := (C (2*rho)-factorB rho)*geom
def errorE (rho : ℝ) : PowerSeries ℝ := C (2*rho)*scaledH rho-geom

def seriesT (rho : ℝ) (N : ℕ) : PowerSeries ℝ :=
  (trunc (N+1) ((1-X)*scaledH rho) : Polynomial ℝ)

def residualP (rho : ℝ) (N : ℕ) : PowerSeries ℝ := 1-seriesT rho N * factorB rho
def forcedD (rho : ℝ) (N : ℕ) : PowerSeries ℝ := seriesT rho N * forcingJ rho

theorem geom_inverse : geom * (1-X) = 1 := mk_one_mul_one_sub_eq_one ℝ

theorem scaledH_coeff (rho : ℝ) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    coeff n (scaledH rho) = rho ^ n * (row n j).eval 1 / n.factorial := by
  rw [scaledH, ← free_series hj, coeff_rescale]
  simp [momentSeries, markedCount_zero, mul_div_assoc]

theorem errorE_coeff (rho : ℝ) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    coeff n (errorE rho) = 2*rho^(n+1)*(row n j).eval 1/n.factorial-1 := by
  rw [errorE, map_sub, coeff_C_mul, scaledH_coeff rho hj, pow_succ]
  simp only [geom, coeff_mk, Pi.one_apply]
  ring

private theorem rescaled_inverse (rho : ℝ) : (2-rescale rho (PowerSeries.exp ℝ))*scaledH rho = 1 := by
  have h : ((2:PowerSeries ℝ)-PowerSeries.exp ℝ)*((2:PowerSeries ℝ)-PowerSeries.exp ℝ)⁻¹=1 := by
    apply PowerSeries.mul_inv_cancel
    rw [map_sub, constantCoeff_exp, show (2 : PowerSeries ℝ) = 1+1 by norm_num, map_add, map_one]
    norm_num
  simpa only [scaledH, show (2 : PowerSeries ℝ) = 1+1 by norm_num, map_mul, map_sub, map_add, map_one]  using congrArg (rescale rho) h

theorem source_identity (rho : ℝ) : factorB rho*errorE rho = forcingJ rho := by
  unfold errorE forcingJ
  have h : factorB rho*scaledH rho = geom := by
    rw [factorB, mul_right_comm, rescaled_inverse, one_mul]
  linear_combination C (2*rho) * h

theorem original_residual_identity (rho : ℝ) (N : ℕ) :
    errorE rho = forcedD rho N + residualP rho N * errorE rho :=
  residual_identity _ _ _ _ (source_identity rho)

private theorem exact_multiplier (rho : ℝ) : ((1-X)*scaledH rho)*factorB rho = 1 := by
  calc
    _ = ((2-rescale rho (PowerSeries.exp ℝ))*scaledH rho)*(geom*(1-X)) := by unfold factorB; ring
    _ = _ := by rw [rescaled_inverse, geom_inverse, mul_one]

theorem seriesT_coeff (rho : ℝ) (N n : ℕ) : coeff n (seriesT rho N) =
    if n ≤ N then coeff n ((1-X)*scaledH rho) else 0 := by
  simp [seriesT, Polynomial.coeff_coe, coeff_trunc]

theorem residualP_early (rho : ℝ) {n N : ℕ} (hn : n ≤ N) : coeff n (residualP rho N) = 0 := by
  rw [residualP, map_sub, sub_eq_zero, ← exact_multiplier rho]
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl (fun v hv ↦ ?_)
  have hv1 := mem_antidiagonal.mp hv
  rw [seriesT_coeff, if_pos (by omega)]

/-- Scalar induction consumes only the finite initial and majorant budgets for the true series. -/
theorem original_error_of_budget (rho : ℝ) (N : ℕ) (R M : ℝ) (hR : 0 ≤ R)
    (initial : ∀ n ≤ N, |coeff n (errorE rho)| *R^n ≤ M)
    (budget : ∀ n > N, |coeff n (forcedD rho N)| *R^n +
      (∑ i ∈ range n, |coeff (i+1) (residualP rho N)| *R^(i+1))*M ≤ M)
    {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    |2*rho^(n+1)*(row n j).eval 1/n.factorial-1| *R^n ≤ M := by
  rw [← errorE_coeff rho hj]
  exact weighted_error _ _ _ (original_residual_identity rho N)
    (residualP_early rho (Nat.zero_le _)) N R M hR initial budget n

#print axioms errorE_coeff
#print axioms source_identity
#print axioms seriesT_coeff
#print axioms residualP_early
#print axioms original_error_of_budget

end OrderedPartitions.Renewal
