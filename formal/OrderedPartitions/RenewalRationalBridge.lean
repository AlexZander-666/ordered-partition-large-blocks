import OrderedPartitions.RenewalTailCutoff

noncomputable section
open Finset PowerSeries
namespace OrderedPartitions.Renewal

def finiteCheckError (L U : ℚ) (f : ℕ → ℕ) (i : ℕ) : ℚ :=
  8^i * max |2*L^(i+1)*f i/i.factorial-1| |2*U^(i+1)*f i/i.factorial-1|

def finiteTapBound (L U : ℚ) (f : ℕ → ℕ) : ℕ → ℚ
  | 0 => 1
  | i+1 => 8^(i+1)*U^i *
    max |L*f (i+1)-(i+1)*f i| |U*f (i+1)-(i+1)*f i| / (i+1).factorial

def finiteExpTail (a : ℚ) (endIndex lo : ℕ) : ℚ :=
  (∑ u ∈ range (endIndex+1-lo), a^(u+lo)/(u+lo).factorial) +
    2*a^(endIndex+1)/(endIndex+1).factorial

def finiteCost (L U : ℚ) (f : ℕ → ℕ) (c : ℚ) (d : ℕ) : ℚ :=
  ∑ i ∈ range 49, finiteTapBound L U f i * (c/8^d *
    finiteExpTail (8*U) 64 (49-i+d))

private theorem abs_interval {a t b : ℝ} (hl : a ≤ t) (hu : t ≤ b) : |t| ≤ max |a| |b| := by
  rw [abs_le]
  constructor
  · have h := le_max_left |a| |b|
    linarith [neg_abs_le a]
  · exact hu.trans ((le_abs_self b).trans (le_max_right _ _))

theorem error_from_interval {L U : ℚ} (h0 : 0 ≤ L) {rho : ℝ} (hl : (L:ℝ) ≤ rho)
    (hu : rho ≤ (U:ℝ)) (f : ℕ→ℕ) (i : ℕ) (hf : (row i 1).eval 1 = f i) :
    |coeff i (errorE rho)| * 8^i ≤ (finiteCheckError L U f i : ℝ) := by
  rw [errorE_coeff rho (j:=1) (by omega), hf, finiteCheckError]
  push_cast
  rw [mul_comm (abs _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply abs_interval
  · gcongr
  · gcongr
    exact (show (0:ℝ) ≤ L by exact_mod_cast h0).trans hl

theorem tap_from_interval {L U : ℚ} (h0 : 0 ≤ L) {rho : ℝ} (hl : (L:ℝ) ≤ rho)
    (hu : rho ≤ (U:ℝ)) (f : ℕ→ℕ) {N i : ℕ} (hi : i ≤ N)
    (hf : ∀ s ≤ N, (row s 1).eval 1 = f s) :
    |coeff i (seriesT rho N)| * 8^i ≤ (finiteTapBound L U f i : ℝ) := by
  have hr := (show (0:ℝ) ≤ L by exact_mod_cast h0).trans hl
  have hU := hr.trans hu
  cases i with
  | zero => simp [t_zero, finiteTapBound]
  | succ i =>
    rw [t_succ rho hi (j:=1) (by omega), hf (i+1) hi, hf i (by omega), finiteTapBound]
    push_cast
    rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hr _), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (i+1).factorial)]
    have inner : |rho * (f (i+1) : ℝ) - ((i:ℝ)+1)*f i| ≤
        max |(L:ℝ)*f (i+1)-((i:ℝ)+1)*f i| |(U:ℝ)*f (i+1)-((i:ℝ)+1)*f i| := by
      apply abs_interval <;> gcongr
    calc
      _ = (8^(i+1)*rho^i*|rho*(f (i+1):ℝ)-((i:ℝ)+1)*f i|)/(i+1).factorial := by ring
      _ ≤ _ := by gcongr

theorem finiteCost_bound {L U : ℚ} (h0 : 0 ≤ L) {rho : ℝ} (hl : (L:ℝ) ≤ rho)
    (hu : rho ≤ (U:ℝ)) (hU : 16*U ≤ 66) (f : ℕ→ℕ)
    (hf : ∀ i ≤ 48, (row i 1).eval 1 = f i) {c : ℚ} (hc : 0 ≤ c) {d : ℕ} (hd : d ≤ 16) :
    tailCost rho 8 c 48 d ≤ (finiteCost L U f c d : ℝ) := by
  have hR := (show (0:ℝ) ≤ L by exact_mod_cast h0).trans hl
  have a : 8*rho ≤ 8*(U:ℝ) := by linarith
  have guard : 2*(8*(U:ℝ)) ≤ (64:ℝ)+2 := by exact_mod_cast (by linarith : 2*(8*U) ≤ 64+2)
  apply (tailCost_le_finite hR (show (0:ℝ)<8 by norm_num) (show (0:ℝ) ≤ c by exact_mod_cast hc)
    a 48 d 64 guard (by omega) (fun i ↦ (finiteTapBound L U f i : ℝ))
    (fun i hi ↦ tap_from_interval h0 hl hu f hi hf)).trans
  unfold finiteCost finiteExpTail
  push_cast
  apply le_of_eq
  apply sum_congr rfl
  intro i _
  simp [q, mul_div_assoc]

/-- The only numerical inputs are inequalities over rationals. The Bell table must agree
with the original row on its entire finite range. -/
theorem original_error_from_rational {L U : ℚ} (h0 : 0 ≤ L)
    (hl : (L:ℝ) ≤ Real.log 2) (hu : Real.log 2 ≤ (U:ℝ)) (hU : 16*U ≤ 66)
    (f : ℕ→ℕ) (hf : ∀ i ≤ 48, (row i 1).eval 1 = f i)
    (initial : ∀ i ≤ 48, finiteCheckError L U f i ≤ 1/2)
    (rc : finiteCost L U f 2 1 ≤ 697279/1000000)
    (fc : finiteCost L U f 4 2 ≤ 131844/1000000)
    {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    |2 * (Real.log 2)^(n+1) * (row n j).eval 1/n.factorial-1| ≤ 1/(2*8^n) := by
  apply ordered_bell_error_of_three_checks _ _ _ hj
  · intro i hi
    exact (error_from_interval h0 hl hu f i (hf i hi)).trans (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (initial i hi))
  · have h := finiteCost_bound h0 hl hu hU f hf (c:=2) (by norm_num) (d:=1) (by norm_num)
    norm_num only [Rat.cast_ofNat] at h
    exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr rc)
  · have h := finiteCost_bound h0 hl hu hU f hf (c:=4) (by norm_num) (d:=2) (by norm_num)
    norm_num only [Rat.cast_ofNat] at h
    exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr fc)

#print axioms original_error_from_rational
#print axioms error_from_interval
#print axioms tap_from_interval
#print axioms finiteCost_bound

end OrderedPartitions.Renewal
