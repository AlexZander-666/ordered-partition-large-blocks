import OrderedPartitions.QuadraticActual

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

private theorem endpoints (j : ℕ) :
    constantCoeff (markerB j) = 1 ∧ coeff 1 (markerB j) = rho/(j+1) ∧
    constantCoeff K = 2*rho ∧ coeff 1 K = (2*rho)*rho := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [coeff_zero_eq_constantCoeff_apply] using marker_zero j
  · simpa [marker_zero] using marker_step j 0
  · rw [← coeff_zero_eq_constantCoeff_apply,k_row (j:=1) (by decide),row_zero (by decide)]
    simp
  · rw [k_row (j:=1) (by decide),RenewalData.bell_real 1 (by decide),show RenewalData.bell 1=1 by rfl]
    simp

/-- The first two nonzero coefficients of the normalized true h-marked numerator. -/
theorem moment_entry_and_successor {j : ℕ} (hj : 1≤j) (h : ℕ) :
    normalizedMoment (h*j) j h = (2*rho)^(h+1)/coeff (h*j) K ∧
    normalizedMoment (h*j+1) j h =
      (2*rho)^(h+1)*(((h:ℝ)+1)*rho+h*rho/(j+1))/coeff (h*j+1) K := by
  obtain ⟨b0,b1,k0,k1⟩ := endpoints j
  constructor
  · simpa [coeff_zero_eq_constantCoeff_apply,b0,k0] using normalizedMoment_coeff hj h 0
  · rw [show h*j+1=1+h*j by omega,normalizedMoment_coeff hj h 1]
    congr 1
    rw [coeff_one_mul,coeff_one_pow,coeff_one_pow]
    simp only [map_pow,b0,b1,k0,k1,one_pow,mul_one,Nat.add_sub_cancel, Nat.cast_add,Nat.cast_one]
    rw [pow_succ (2*rho) h]
    ring

private theorem rho_tight : (693:ℝ)/1000<rho ∧ rho<694/1000 := by
  obtain ⟨h,h'⟩ := Renewal.log_two_interval
  have lo : (693/1000:ℚ) < Renewal.rhoLower := by decide +kernel
  have hi : Renewal.rhoUpper < (694/1000:ℚ) := by decide +kernel
  constructor
  · apply lt_of_lt_of_le _ h
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr lo
  · apply lt_of_le_of_lt h'
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr hi

private theorem k_tight {n : ℕ} (hn : 3≤n) :
    (999:ℝ)/1000 ≤ coeff n K ∧ coeff n K ≤ 1001/1000 := by
  have pot : (8:ℝ)^3≤8^n := pow_le_pow_right₀ (by norm_num) hn
  have cap : (1:ℝ)/(2*8^n) ≤ 1/1000 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have e := abs_le.mp ((eps_bound n).trans cap)
  unfold eps at e
  constructor <;> linarith [e.1,e.2]

private theorem four_bounds :
    (1386/1000:ℝ)^4 ≤ (2*rho)^4 ∧ (2*rho)^4 ≤ (1388/1000:ℝ)^4 := by
  obtain ⟨l,u⟩ := rho_tight
  exact ⟨pow_le_pow_left₀ (by norm_num) (by linarith) 4,
    pow_le_pow_left₀ (by linarith) (by linarith) 4⟩

theorem cubic_entry_bounds {j : ℕ} (hj : 2≤j) :
    3.67 < normalizedMoment (3*j) j 3 ∧ normalizedMoment (3*j) j 3 < 3.72 := by
  rw [normalized_cubic_at (by omega : 1≤j)]
  obtain ⟨l,u⟩ := k_tight (n:=3*j) (by omega)
  have pos := k_pos (3*j)
  exact ⟨(lt_div_iff₀ pos).mpr (by linarith [four_bounds.1]),
    (div_lt_iff₀ pos).mpr (by linarith [four_bounds.2])⟩

/-- The advertised upper bound is sharp as a threshold: j=2 is its sole exception
among the admissible thresholds. The lower bound is uniform even at j=2. -/
theorem cubic_increment_bounds {j : ℕ} (hj : 2≤j) :
    let f := normalizedMoment (3*j+1) j 3-normalizedMoment (3*j) j 3
    6 < f ∧ (f < 9 ↔ 3≤j) := by
  dsimp only
  have succ := (moment_entry_and_successor (j:=j) (by omega) 3).2
  norm_num only [Nat.cast_ofNat,show (3:ℝ)+1=4 by norm_num] at succ
  obtain ⟨cl,cu⟩ := cubic_entry_bounds hj
  obtain ⟨kl,ku⟩ := k_tight (n:=3*j+1) (by omega)
  have pos := k_pos (3*j+1)
  have rr := rho_tight
  have r0 : 0<rho := by linarith [rr.1]
  have base : (693/1000:ℝ)*4 ≤ 4*rho+3*rho/(j+1) := by
    linarith [show 0≤3*rho/(j+1) by positivity,rr.1]
  have low := mul_le_mul four_bounds.1 base (by norm_num) (by positivity)
  rw [succ]
  constructor
  · have h : (9.72:ℝ) < (2*rho)^4*(4*rho+3*rho/(j+1))/coeff (3*j+1) K :=
      (lt_div_iff₀ pos).mpr (by linarith)
    linarith
  · constructor
    · intro h
      by_contra! small
      obtain rfl : j=2 := by omega
      norm_num at h
      have bd : (693/1000:ℝ)*5 ≤ 4*rho+3*rho/(2+1:ℝ) := by linarith [rr.1]
      have z := mul_le_mul four_bounds.1 bd (by norm_num) (by positivity)
      norm_num at z
      have h9 : (12.72:ℝ) < (2*rho)^4*(4*rho+3*rho/(2+1:ℝ))/coeff 7 K :=
        (lt_div_iff₀ pos).mpr (by norm_num at z ⊢; linarith)
      norm_num at h9
      linarith
    · intro large
      have z : 3*rho/(j+1) ≤ 3*(694/1000)/4 := (div_le_iff₀ (by positivity)).mpr (by
        have J : (3:ℝ)≤j := by exact_mod_cast large
        linarith [rr.2])
      have w := mul_le_mul four_bounds.2 (show 4*rho+3*rho/(j+1)≤(694/1000)*(4+3/4) by linarith [rr.2])
        (by positivity) (by norm_num)
      have hi : (2*rho)^4*(4*rho+3*rho/(j+1))/coeff (3*j+1) K < 12.67 :=
        (div_lt_iff₀ pos).mpr (by linarith)
      linarith

#print axioms moment_entry_and_successor
#print axioms cubic_entry_bounds
#print axioms cubic_increment_bounds
end OrderedPartitions.Kernel
