import OrderedPartitions.RenewalVerified
import Mathlib.RingTheory.PowerSeries.Derivative

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

def rho : ℝ := Real.log 2
def K : PowerSeries ℝ := C (2*rho) * Renewal.scaledH rho
def eps (s : ℕ) : ℝ := coeff s K - 1
def g (s : ℕ) : ℝ := coeff s (K^2)
def w (s : ℕ) : ℝ := coeff s (K^3)

theorem rho_interval : 69/100 < rho ∧ rho < 7/10 := by
  obtain ⟨h,h'⟩ := Renewal.log_two_interval
  have lo : (69/100:ℚ) < Renewal.rhoLower := by decide +kernel
  have hi : Renewal.rhoUpper < (7/10:ℚ) := by decide +kernel
  constructor
  · apply lt_of_lt_of_le _ h
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr lo
  · apply lt_of_le_of_lt h'
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr hi

theorem eps_bound (s : ℕ) : |eps s| ≤ 1/(2*8^s) := by
  have he := Renewal.ordered_bell_geometric_error (j:=1) (by omega) s
  rw [← Renewal.errorE_coeff (Real.log 2) (j:=1) (by omega)] at he
  simpa [eps, K, Renewal.errorE, Renewal.geom_coeff, rho] using he

private theorem derivative_rescale (r : ℝ) (f : PowerSeries ℝ) :
    derivative ℝ (rescale r f) = C r * rescale r (derivative ℝ f) := by
  ext n
  rw [coeff_derivative, coeff_rescale, coeff_C_mul, coeff_rescale, coeff_derivative]
  simp [pow_succ]
  ring

private theorem unscaled_derivative :
    let H := ((2:PowerSeries ℝ)-PowerSeries.exp ℝ)⁻¹
    derivative ℝ H = 2*H^2-H := by
  let D := ((2:PowerSeries ℝ)-PowerSeries.exp ℝ)
  have hi : D⁻¹ * D = 1 := by
    apply PowerSeries.inv_mul_cancel
    simp [D, show (2 : PowerSeries ℝ)=1+1 by norm_num]
  change derivative ℝ (D⁻¹) = 2*(D⁻¹)^2-D⁻¹
  rw [derivative_inv']
  have hd : derivative ℝ D = -PowerSeries.exp ℝ := by
    simp [D, show (2:PowerSeries ℝ)=1+1 by norm_num, derivative_exp]
  rw [hd, neg_mul_neg]
  dsimp only [D] at hi ⊢
  linear_combination -(2-PowerSeries.exp ℝ)⁻¹ * hi

theorem K_derivative : derivative ℝ K = K^2-C rho*K := by
  unfold K Renewal.scaledH
  rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul, derivative_rescale,
    unscaled_derivative]
  simp only [map_sub, map_mul, map_pow, show (2:PowerSeries ℝ)=1+1 by norm_num, map_add, map_one,
    show (2:ℝ)=1+1 by norm_num]
  ring

theorem g_exact (s : ℕ) : g s = (s+1:ℝ)*(1+eps (s+1)) + rho*(1+eps s) := by
  have h := congrArg (coeff s) K_derivative
  rw [coeff_derivative, map_sub, coeff_C_mul] at h
  unfold eps g
  linarith

private theorem K_second : C (2:ℝ)*K^3 = derivative ℝ (derivative ℝ K) +
    C (3*rho)*derivative ℝ K + C (2*rho^2)*K := by
  conv_rhs => lhs; lhs; rw [K_derivative]
  rw [map_sub, derivative_pow, Derivation.leibniz, derivative_C, smul_zero, add_zero,
    smul_eq_mul, K_derivative]
  simp only [map_mul, map_pow, show (2:ℝ)=1+1 by norm_num, show (3:ℝ)=1+1+1 by norm_num,
    map_add, map_one]
  ring

theorem w_exact (s : ℕ) : w s =
    ((s+1:ℝ)*(s+2)/2)*(1+eps (s+2)) +
    3*rho/2*(s+1)*(1+eps (s+1)) + rho^2*(1+eps s) := by
  have h := congrArg (coeff s) K_second
  rw [coeff_C_mul, map_add, map_add, coeff_derivative, coeff_derivative, coeff_C_mul,
    coeff_derivative, coeff_C_mul] at h
  unfold w eps
  push_cast at h
  linarith

#print axioms eps_bound
#print axioms g_exact
#print axioms w_exact
end OrderedPartitions.Kernel
