import OrderedPartitions.QuadraticNormalized
import OrderedPartitions.AllMoments

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

theorem markScale_pos (j : ℕ) : 0<markScale j := by
  have r : 0<rho := by linarith [rho_interval.1]
  unfold markScale
  positivity

theorem normalized_before {n j h : ℕ} (hj : 1≤j) (hn : n<h*j) :
    normalizedMoment n j h=0 := by
  simp [normalizedMoment,markedCount_before hj hn]

theorem normalized_cubic_at {j : ℕ} (hj : 1≤j) :
    normalizedMoment (3*j) j 3 = (2*rho)^4/coeff (3*j) K := by
  have zB : constantCoeff (markerB j) = 1 := by
    simpa only [coeff_zero_eq_constantCoeff_apply] using marker_zero j
  have zK : constantCoeff K = 2*rho := by
    rw [← coeff_zero_eq_constantCoeff_apply,k_row (j:=1) (by decide), row_zero (by decide)]
    simp
  simpa [coeff_zero_eq_constantCoeff_apply,zB,zK] using normalizedMoment_coeff hj 3 0

theorem original_cubic_boundary {j m : ℕ} (hj : 50≤j) (hm : m<j) :
    let c := normalizedMoment (2*j+m+1) j 3
    0≤c ∧ c≤4 ∧ (c=0 ∨ m=j-1) := by
  dsimp only
  by_cases he : m=j-1
  · rw [show 2*j+m+1=3*j by omega,normalized_cubic_at (by omega : 1≤j)]
    have small : (1:ℝ)/(2*8^(3*j)) ≤ 1/128 := by
      have p : (8:ℝ)^2 ≤ 8^(3*j) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have low := (abs_le.mp ((eps_bound (3*j)).trans small)).1
    unfold eps at low
    have pos := k_pos (3*j)
    have r : 0<rho := by linarith [rho_interval.1]
    have z := pow_le_pow_left₀ (show 0≤2*rho by positivity)
      (show 2*rho≤7/5 by linarith [rho_interval.2]) 4
    exact ⟨by positivity,(div_le_iff₀ pos).mpr (by linarith), Or.inr he⟩
  · rw [normalized_before (by omega : 1≤j) (by omega)]
    norm_num

theorem original_eval_normalized {n j : ℕ} (hj : 1≤j) (hn : n<4*j) (t : ℝ) :
    let O := row n j
    let y := markScale j*(t-1)
    O.eval t = O.eval 1 * (1+normalizedMoment n j 1*y+
      normalizedMoment n j 2*y^2+normalizedMoment n j 3*y^3) := by
  dsimp only
  let p := (row n j).comp (Polynomial.X+1)
  have expand : p = Polynomial.C ((row n j).eval 1) +
      Polynomial.C (markedCount n j 1)*Polynomial.X +
      Polynomial.C (markedCount n j 2)*Polynomial.X^2 +
      Polynomial.C (markedCount n j 3)*Polynomial.X^3 := by
    ext d
    change markedCount n j d = _
    rcases d with _|_|_|_|d
    · simp [markedCount_zero]
    · simp
    · simp
    · simp
    · have h := markedCount_before hj (lt_of_lt_of_le hn (Nat.mul_le_mul_right j (by omega : 4≤d+4)))
      simpa [show d+1+1+1+1≠3 by omega, show 3≠d+1+1+1+1 by omega,
        show 2≠d+1+1+1+1 by omega, show 1≠d+1+1+1+1 by omega] using h
  have e := congrArg (Polynomial.eval (t-1)) expand
  simp [p,Polynomial.eval_comp] at e
  have v := original_eval_pos hj n
  have d := markScale_pos j
  rw [e]
  unfold normalizedMoment
  field_simp

#print axioms original_cubic_boundary
#print axioms original_eval_normalized
end OrderedPartitions.Kernel
