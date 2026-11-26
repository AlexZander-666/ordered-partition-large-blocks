import OrderedPartitions.QuadraticConvolution

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

private theorem polynomial_decay {n : ℕ} (hn : 100≤n) :
    2000*((n:ℝ)+6)^2 ≤ (8:ℝ)^n := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
    rw [pow_succ (8:ℝ) n]; push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ)]

private theorem normalization_price {n : ℕ} (hn : 100≤n) {a : ℝ}
    (non : 0≤a) (cap : a≤((n:ℝ)+6)^2) : |a/coeff n K-a| ≤ 1/2000 := by
  let k := coeff n K
  have pos : 0<k := k_pos n
  have e : |k-1| ≤ 1/(2*8^n) := eps_bound n
  have e' : |k-1| ≤ 1/2 := e.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by
    linarith [one_le_pow₀ (show (1:ℝ)≤8 by norm_num) (n:=n)]))
  have half : 1/2 ≤ k := by linarith [(abs_le.mp e').1]
  change |a/k-a| ≤ _
  rw [show a/k-a= -(a*(k-1))/k by field_simp; ring,abs_div,abs_neg,abs_mul,
    abs_of_nonneg non,abs_of_pos pos]
  apply (div_le_iff₀ pos).mpr
  have prod := mul_le_mul cap e (abs_nonneg _) (sq_nonneg _)
  have pin : ((n:ℝ)+6)^2*(1/(2*8^n)) ≤ 1/4000 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [polynomial_decay hn]
  linarith [prod.trans pin]

private theorem linear_price {n s j : ℕ} (hn : 100≤n) (sj : 50≤j) (sn : s≤n) :
    |linearRaw j s/coeff n K - linearRaw j s| ≤ 1/2000 := by
  have b := raw_linear_bounds sj s
  have se : (s:ℝ) ≤ n := by exact_mod_cast sn
  apply normalization_price hn
  · linarith [b.1,Nat.cast_nonneg (α:=ℝ) s]
  · nlinarith [b.2,Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ)]

private theorem quadratic_price {n s j : ℕ} (hn : 100≤n) (sj : 50≤j) (sn : s≤n) :
    |quadraticRaw j s/coeff n K - quadraticRaw j s| ≤ 1/2000 := by
  have b := raw_quadratic_bounds sj s
  have se : (s:ℝ) ≤ n := by exact_mod_cast sn
  apply normalization_price hn
  · linarith [b.1,show (0:ℝ)≤(s+1:ℝ)*(s+2)/2 by positivity]
  · have sm : ((s:ℝ)+4)^2 ≤ ((n:ℝ)+6)^2 := by
      apply pow_le_pow_left₀ (by positivity) (by linarith)
    nlinarith [b.2,sq_nonneg ((n:ℝ)+6)]

theorem normalized_linear (j s : ℕ) (hj : 1≤j) :
    normalizedMoment (s+j) j 1 = linearRaw j s/coeff (s+j) K := by
  simpa only [one_mul, pow_one, linearRaw] using normalizedMoment_coeff hj 1 s

theorem normalized_quadratic (j s : ℕ) (hj : 1≤j) :
    normalizedMoment (s+2*j) j 2 = quadraticRaw j s/coeff (s+2*j) K :=
  normalizedMoment_coeff hj 2 s

/-- Equation (3) for the coefficients of the two actual normalized rows. -/
theorem original_quadratic_estimates {j : ℕ} (hj : 50≤j) (m : ℕ) :
    let n := 2*j+m
    let a := normalizedMoment n j 1
    let b := normalizedMoment n j 2
    let da := normalizedMoment (n+1) j 1-a
    let db := normalizedMoment (n+1) j 2-b
    (j:ℝ)+m ≤ a ∧ a ≤ 1.02*((j:ℝ)+m+3) ∧
    0.99 ≤ da ∧ da ≤ 1.04 ∧
    0.49*((m:ℝ)+1)*(m+2) ≤ b ∧ b ≤ 0.52*((m:ℝ)+4)^2 ∧
    (m:ℝ)+1.9 ≤ db ∧ db ≤ 1.04*((m:ℝ)+4) := by
  let n := 2*j+m
  let s := j+m
  have hn : 100≤n := by dsimp [n]; omega
  have hs : 50≤s := by dsimp [s]; omega
  have sn : s≤n := by dsimp [s,n]; omega
  have mn : m≤n := by dsimp [n]; omega
  have one : 1≤j := by omega
  have al : normalizedMoment n j 1 = linearRaw j s/coeff n K := by
    rw [show n=s+j by dsimp [s,n]; omega, normalized_linear j s one]
  have al' : normalizedMoment (n+1) j 1 = linearRaw j (s+1)/coeff (n+1) K := by
    rw [show n+1=(s+1)+j by dsimp [s,n]; omega, normalized_linear j (s+1) one]
  have be : normalizedMoment n j 2 = quadraticRaw j m/coeff n K := by
    rw [show n=m+2*j by dsimp [n]; omega, normalized_quadratic j m one]
  have be' : normalizedMoment (n+1) j 2 = quadraticRaw j (m+1)/coeff (n+1) K := by
    rw [show n+1=(m+1)+2*j by dsimp [n]; omega, normalized_quadratic j (m+1) one]
  change (j:ℝ)+m ≤ normalizedMoment n j 1 ∧ _
  change (j:ℝ)+m ≤ normalizedMoment n j 1 ∧
    normalizedMoment n j 1 ≤ 1.02*((j:ℝ)+m+3) ∧
    0.99 ≤ normalizedMoment (n+1) j 1-normalizedMoment n j 1 ∧
    normalizedMoment (n+1) j 1-normalizedMoment n j 1 ≤ 1.04 ∧
    0.49*((m:ℝ)+1)*(m+2) ≤ normalizedMoment n j 2 ∧
    normalizedMoment n j 2 ≤ 0.52*((m:ℝ)+4)^2 ∧
    (m:ℝ)+1.9 ≤ normalizedMoment (n+1) j 2-normalizedMoment n j 2 ∧
    normalizedMoment (n+1) j 2-normalizedMoment n j 2 ≤ 1.04*((m:ℝ)+4)
  rw [al,al',be,be']
  have ap := abs_le.mp (linear_price hn hj sn)
  have ap' := abs_le.mp (linear_price (n:=n+1) (by omega) hj (s:=s+1) (by omega))
  have bp := abs_le.mp (quadratic_price hn hj mn)
  have bp' := abs_le.mp (quadratic_price (n:=n+1) (by omega) hj (s:=m+1) (by omega))
  have aa := raw_linear_bounds hj s
  have bb := raw_quadratic_bounds hj m
  have da := raw_linear_increment hj hs
  have db := raw_quadratic_increment hj m
  have eqs : (s:ℝ) = (j:ℝ)+m := by simp [s]
  rw [eqs] at aa
  have z := Nat.cast_nonneg (α:=ℝ) m
  have zj := Nat.cast_nonneg (α:=ℝ) j
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · linarith [ap.1,aa.1]
  · linarith [ap.2,aa.2]
  · linarith [ap.2,ap'.1,da.1]
  · linarith [ap.1,ap'.2,da.2]
  · nlinarith [bp.1,bb.1,sq_nonneg (m:ℝ)]
  · nlinarith [bp.2,bb.2,sq_nonneg (m:ℝ)]
  · linarith [bp.2,bp'.1,db.1]
  · linarith [bp.1,bp'.2,db.2]

#print axioms original_quadratic_estimates
end OrderedPartitions.Kernel
