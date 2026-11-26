import OrderedPartitions.CubicQuarticOrder

/-! A normalized cubic and the quadratic difference criterion with an optional quartic correction. -/
noncomputable section
open Polynomial
namespace OrderedPartitions.QuadraticOrder

def quartic (a b c d e : ℝ) : ℝ[X] := cubic a b c d + C e*X^4

@[simp] theorem eval_quartic (a b c d e y : ℝ) :
    (quartic a b c d e).eval y=a+b*y+c*y^2+d*y^3+e*y^4 := by simp [quartic]

theorem cubic_leading {a b c d : ℝ} (hd : d≠0) :
    (cubic a b c d).natDegree=3 ∧ (cubic a b c d).leadingCoeff=d := by
  have deg : (cubic a b c d).natDegree=3 := by unfold cubic quadratic; compute_degree!
  refine ⟨deg,?_⟩
  rw [leadingCoeff,deg]
  simp [cubic,quadratic]

theorem quartic_leading {a b c d e : ℝ} (he : e≠0) :
    (quartic a b c d e).natDegree=4 ∧ (quartic a b c d e).leadingCoeff=e := by
  have deg : (quartic a b c d e).natDegree=4 := by unfold quartic cubic quadratic; compute_degree!
  refine ⟨deg,?_⟩
  rw [leadingCoeff,deg]
  simp [quartic,cubic,quadratic]

/-- The enclosures on d,e,f apply to the corrected coefficients. The exact parameter
k is zero on the cubic plateau and positive at the first quartic. -/
theorem normalized_cubic_chamber {a b c d e f k V : ℝ} (ha : 0≤a) (hb : 0<b)
    (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hk : 0≤k)
    (capacity : d*f/e^2≤4/25)
    (cap : ∀ v : ℝ, 1≤v → v≤5/4 → 1-v+(d*f/e^2)*v^2=0 → v≤V)
    (near : V*d*max 0 (b*d-f)<(a*d-e)*e)
    (far : V*a*f/(b*e)+c*e/(b*f)<1) :
    CubicAdjacent (cubic 1 a b c) (quartic 1 (a+d+k) (b+e+k*a) (c+f+k*b) (k*c)) (0<k) := by
  let p := cubic 1 a b c
  let q := quartic 1 (a+d+k) (b+e+k*a) (c+f+k*b) (k*c)
  obtain ⟨w,z,wp,wz,fac,pw,pz⟩ := CubicChamber.separation_points ha hb hc.le hd he hf capacity cap near far
  have old := cubic_leading (a:=1) (b:=a) (c:=b) hc.ne'
  apply cubic_adjacent_at_points (p:=p) (q:=q) old.1 (old.2.symm ▸ hc)
    (by simp [p]) (by simp [q]) _ _ wp wz hf
  · simp only [p,eval_cubic]; nlinarith only [pz]
  · simp only [p,eval_cubic]; nlinarith only [pw]
  · intro x hx
    have pe : 1+a*x+b*x^2+c*x^3=0 := by simpa [p] using hx
    rw [← fac]
    simp only [q,eval_quartic]
    linear_combination (1+k*x)*pe
  · intro h
    have h0 := le_antisymm (le_of_not_gt h) hk
    subst k
    unfold q quartic cubic quadratic
    simp
    compute_degree!
  · intro pos
    have e0 := mul_pos pos hc
    have big := quartic_leading (a:=1) (b:=a+d+k) (c:=b+e+k*a) (d:=c+f+k*b) e0.ne'
    exact ⟨big.1,big.2.symm ▸ e0⟩

/-- Dimensionless cell bounds can be checked with the arbitrary positive scale J.
Only the old coefficients carry powers J, J², J³; the first corrected difference
is unscaled, while the other corrected differences carry J and J². -/
theorem normalized_chamber_from_scaled {a b c d e f k V J : ℝ} (hJ : 0<J)
    (ha : 0≤a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hk : 0≤k)
    (capacity : d*(f/J^2)/(e/J)^2≤4/25)
    (cap : ∀ v : ℝ, 1≤v → v≤5/4 → 1-v+d*(f/J^2)/(e/J)^2*v^2=0 → v≤V)
    (near : V*d*max 0 (b/J^2*d-f/J^2)<(a/J*d-e/J)*(e/J))
    (far : V*(a/J)*(f/J^2)/((b/J^2)*(e/J))+
      (c/J^3)*(e/J)/((b/J^2)*(f/J^2))<1) :
    CubicAdjacent (cubic 1 a b c) (quartic 1 (a+d+k) (b+e+k*a) (c+f+k*b) (k*c)) (0<k) := by
  have h1 : d*(f/J^2)/(e/J)^2=d*f/e^2 := by field_simp
  rw [h1] at capacity cap
  apply normalized_cubic_chamber ha hb hc hd he hf hk capacity cap
  · have inner : b/J^2*d-f/J^2=(b*d-f)/J^2 := by ring
    have M := max_div_div_right (sq_nonneg J) 0 (b*d-f)
    rw [zero_div] at M
    rw [inner,M] at near
    have r : (a/J*d-e/J)*(e/J)=((a*d-e)*e)/J^2 := by field_simp
    rw [r,← mul_div_assoc] at near
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hJ)).mp near
  · convert far using 1
    field_simp

#print axioms normalized_chamber_from_scaled
#print axioms normalized_cubic_chamber
end OrderedPartitions.QuadraticOrder
