import OrderedPartitions.RenewalKernel

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

/-- Coefficient of the next power from the Riccati identity for the true renewal kernel. -/
theorem power_coeff_step (h s : ℕ) :
    coeff s (K ^ (h+2)) =
      ((s:ℝ)+1)/((h:ℝ)+1) * coeff (s+1) (K ^ (h+1)) +
      rho * coeff s (K ^ (h+1)) := by
  have eqn : derivative ℝ (K ^ (h+1)) =
      C ((h:ℝ)+1) * K ^ (h+2) - C (((h:ℝ)+1)*rho) * K ^ (h+1) := by
    rw [derivative_pow, K_derivative, Nat.add_sub_cancel, map_mul, map_add,
      map_one, map_natCast, pow_succ K (h+1), pow_succ K h]
    push_cast
    ring
  have c := congrArg (coeff s) eqn
  simp only [coeff_derivative, map_sub, coeff_C_mul] at c
  field_simp
  linarith only [c]

/-- The main term is obtained by replacing every coefficient of the first power by one. -/
def powerMain : ℕ → ℕ → ℝ
  | 0, _ => 1
  | h+1, s => ((s:ℝ)+1)/((h:ℝ)+1) * powerMain h (s+1) + rho * powerMain h s

theorem powerMain_pos (h s : ℕ) : 0 < powerMain h s := by
  induction h generalizing s with
  | zero => simp [powerMain]
  | succ h ih =>
    have hr : 0 < rho := lt_trans (by norm_num) rho_interval.1
    exact add_pos (mul_pos (by positivity) (ih (s+1))) (mul_pos hr (ih s))

/-- A relative error bound valid for all powers and all coefficient indices at once. -/
theorem all_power_relative_error (h s : ℕ) :
    |coeff s (K ^ (h+1)) - powerMain h s| ≤ powerMain h s / (2*8^s) := by
  induction h generalizing s with
  | zero => simpa [eps, powerMain] using eps_bound s
  | succ h ih =>
    let u : ℝ := ((s:ℝ)+1)/((h:ℝ)+1)
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hr : 0 ≤ rho := le_of_lt (lt_trans (by norm_num) rho_interval.1)
    have monotone : powerMain h (s+1) / (2*8^(s+1)) ≤ powerMain h (s+1) / (2*8^s) := by
      apply div_le_div_of_nonneg_left (powerMain_pos _ _).le (by positivity)
      rw [pow_succ]; nlinarith only [show (0:ℝ) ≤ 8^s by positivity]
    rw [power_coeff_step h s, powerMain]
    change |u * _ + rho * _ - (u * _ + rho * _)| ≤ _
    rw [show u * coeff (s+1) (K^(h+1)) + rho * coeff s (K^(h+1)) -
          (u*powerMain h (s+1) + rho*powerMain h s) =
          u*(coeff (s+1) (K^(h+1))-powerMain h (s+1)) +
          rho*(coeff s (K^(h+1))-powerMain h s) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hr]
    calc
      _ ≤ u * (powerMain h (s+1)/(2*8^s)) + rho * (powerMain h s/(2*8^s)) :=
        add_le_add (mul_le_mul_of_nonneg_left ((ih (s+1)).trans monotone) hu)
          (mul_le_mul_of_nonneg_left (ih s) hr)
      _ = _ := by dsimp only [u]; ring

#print axioms power_coeff_step
#print axioms all_power_relative_error
end OrderedPartitions.Kernel
