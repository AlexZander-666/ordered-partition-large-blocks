import OrderedPartitions.CubicFourthKernel

noncomputable section
open Finset PowerSeries
namespace OrderedPartitions.Kernel

def cq (j : ℕ) : ℝ := 1/j
def cMass (j : ℕ) : ℝ := (1-0.7*cq j)⁻¹
def cEta (j : ℕ) : ℝ := cq j/100
def cBeta (j : ℕ) : ℝ := 0.69*cq j/(1+cq j)
def cWeight (j h i : ℕ) : ℝ := coeff i (markerB j ^ h)
def cubicRaw (j s : ℕ) : ℝ := coeff s (markerB j^3*K^4)

theorem cq_pos {j : ℕ} (hj : 64≤j) : 0<cq j := by
  have J : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  unfold cq; positivity

theorem cq_bound {j : ℕ} (hj : 64≤j) : cq j≤1/64 := by
  unfold cq
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hj)

theorem mass_pos {j : ℕ} (hj : 64≤j) : 0<cMass j := by
  unfold cMass
  exact inv_pos.mpr (by linarith [cq_bound hj])

theorem mass_limits {j : ℕ} (hj : 64≤j) : 1≤cMass j ∧ cMass j≤1.02 := by
  have pos : 0<1-0.7*cq j := by linarith [cq_bound hj]
  unfold cMass; rw [← one_div]
  exact ⟨(le_div_iff₀ pos).mpr (by linarith [cq_pos hj]),(div_le_iff₀ pos).mpr (by linarith [cq_bound hj])⟩

theorem beta_weight {j : ℕ} (hj : 64≤j) : cBeta j≤coeff 1 (markerB j) ∧ coeff 1 (markerB j)≤1 := by
  have J : (64:ℝ)≤j := by exact_mod_cast hj
  have jp : (0:ℝ)<j := by linarith
  rw [show coeff 1 (markerB j)=rho/(j+1) by simpa [marker_zero] using marker_step j 0]
  have e : cBeta j=0.69/(j+1) := by unfold cBeta cq; field_simp
  rw [e]
  exact ⟨div_le_div_of_nonneg_right (by linarith [rho_interval.1]) (by positivity),
    (div_le_iff₀ (by positivity)).mpr (by linarith [rho_interval.2])⟩

theorem first_mass {j : ℕ} (hj : 64≤j) (N : ℕ) : ∑ i ∈ range N, coeff i (markerB j) ≤ cMass j := by
  let r := 0.7*cq j
  have jp : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hr : 0≤r := by dsimp [r]; positivity [cq_pos hj]
  have r1 : r<1 := by dsimp [r]; linarith [cq_bound hj]
  have env (i : ℕ) : coeff i (markerB j) ≤ r^i := by
    induction i with
    | zero => simp [marker_zero]
    | succ i ih =>
      rw [marker_step,pow_succ,mul_div_assoc]
      have rh : 0≤rho := by linarith [rho_interval.1]
      apply mul_le_mul ih _ (by positivity) (pow_nonneg hr _)
      dsimp [r,cq]
      rw [mul_one_div]
      exact div_le_div₀ (by norm_num) (by linarith [rho_interval.2]) jp (by linarith [Nat.cast_nonneg (α:=ℝ) i])
  apply (sum_le_sum (fun i _ ↦ env i)).trans
  change _ ≤ (1-r)⁻¹
  rw [← one_div]
  apply (le_div_iff₀ (by linarith)).mpr
  linarith only [geom_sum_mul r N, pow_nonneg hr N]

theorem cWeight_nonneg (j h i : ℕ) : 0≤cWeight j h i := by
  induction h generalizing i with
  | zero => simp [cWeight,coeff_one]; split <;> norm_num
  | succ h ih =>
    rw [cWeight,pow_succ,coeff_mul]
    exact sum_nonneg (fun p _ ↦ mul_nonneg (ih p.1) (marker_positive j p.2).le)

theorem cWeight_zero (j h : ℕ) : cWeight j h 0=1 := by
  have z : constantCoeff (markerB j)=1 := by simpa only [coeff_zero_eq_constantCoeff_apply] using marker_zero j
  simp [cWeight,coeff_zero_eq_constantCoeff_apply,z]

theorem cWeight_one (j h : ℕ) : cWeight j h 1=h*coeff 1 (markerB j) := by
  have z : constantCoeff (markerB j)=1 := by simpa only [coeff_zero_eq_constantCoeff_apply] using marker_zero j
  simp [cWeight,coeff_one_pow,z]

theorem cWeight_mass {j : ℕ} (hj : 64≤j) (h N : ℕ) :
    ∑ i ∈ range N, cWeight j h i ≤ cMass j^h := by
  induction h generalizing N with
  | zero =>
    simp only [cWeight,pow_zero,coeff_one,sum_ite_eq', mem_range]
    split <;> norm_num
  | succ h ih =>
    have e (i : ℕ) : cWeight j (h+1) i =
        ∑ k ∈ range (i+1), cWeight j h k*coeff (i-k) (markerB j) := by
      rw [cWeight,pow_succ,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rfl
    simp_rw [e]
    rw [sum_range_diag_flip N (fun r s ↦ cWeight j h r *coeff s (markerB j)),pow_succ]
    simp_rw [← mul_sum]
    calc
      _ ≤ ∑ i ∈ range N, cWeight j h i*cMass j := by
        exact sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (first_mass hj _) (cWeight_nonneg j h i))
      _ = _ := (sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (ih _) (mass_pos hj).le

theorem cRaw_conv (j s : ℕ) : cubicRaw j s=convSeq (cWeight j 3) v s := by
  rw [cubicRaw,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rfl

theorem cLinear_conv (j s : ℕ) : linearRaw j s=convSeq (cWeight j 1) g s := by
  rw [linearRaw,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]; simp [convSeq,cWeight,g]

theorem cQuadratic_conv (j s : ℕ) : quadraticRaw j s=convSeq (cWeight j 2) w s := by
  rw [quadraticRaw,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rfl

/-- The two explicitly retained coefficients in a positive convolution. The same
bound applies to a forward difference through the zero-extended difference kernel. -/
theorem conv_two {j h s : ℕ} (hj : 64≤j) (F : ℕ→ℝ) {U : ℝ}
    (pos : ∀i≤s+1, 0≤F i) (cap : ∀i≤s-1, F i≤U) (un : 0≤U) :
    let core := F (s+1)+cWeight j h 1*F s
    core ≤ convSeq (cWeight j h) F (s+1) ∧
      convSeq (cWeight j h) F (s+1) ≤ core+(cMass j^h-1-cWeight j h 1)*U := by
  let weights := cWeight j h
  have mass := cWeight_mass hj h (s+2)
  change ∑ i ∈ range (s+2), weights i ≤ _ at mass
  rw [sum_range_succ' weights,sum_range_succ' (fun i ↦ weights (i+1))] at mass
  have z : weights 0=1 := cWeight_zero j h
  rw [z] at mass
  unfold convSeq
  rw [sum_range_succ',sum_range_succ' (fun i ↦ _)]
  simp only [cWeight_zero,one_mul,Nat.sub_zero,Nat.add_sub_cancel]
  have tail : (0:ℝ)≤∑ i ∈ range s, cWeight j h (i+1+1)*F (s+1-(i+1+1)) :=
    sum_nonneg (fun i _ ↦ mul_nonneg (cWeight_nonneg ..) (pos _ (Nat.sub_le ..)))
  have upper : (∑ i ∈ range s, cWeight j h (i+1+1)*F (s+1-(i+1+1))) ≤
      (∑ i ∈ range s, weights (i+1+1))*U := by
    rw [sum_mul]
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (cap _ (by omega)) (cWeight_nonneg ..)
  have bdd := mul_le_mul_of_nonneg_right (show (∑ i ∈ range s,weights (i+1+1))≤cMass j^h-1-weights 1 by linarith) un
  change _ ≤ _ ∧ _ ≤ _
  simp only [Nat.zero_add] at *
  dsimp [weights] at bdd upper
  constructor <;> linarith

#print axioms cWeight_mass
#print axioms conv_two
end OrderedPartitions.Kernel
