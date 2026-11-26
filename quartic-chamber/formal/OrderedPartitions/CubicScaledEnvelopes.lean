import OrderedPartitions.CubicChamberEnvelopes
import OrderedPartitions.CubicMomentSupport

/-! The true numerator estimates in the dimensionless units u=m/j, q=1/j. -/
noncomputable section
namespace OrderedPartitions.CubicChamber.Box
open OrderedPartitions.Kernel

/-- Values and rank increments in the common affine coordinate. -/
structure ScaledRow where
  a : ℝ
  b : ℝ
  c : ℝ
  d0 : ℝ
  e0 : ℝ
  f0 : ℝ
  κ : ℝ

def actualRow (j m : ℕ) : ScaledRow :=
  let n := 3*j+m
  let A h := normalizedMoment n j h
  let D h := normalizedMoment (n+1) j h-A h
  ⟨A 1/j,A 2/(j:ℝ)^2,A 3/(j:ℝ)^3,D 1,D 2/j,D 3/(j:ℝ)^2,normalizedMoment (n+1) j 4/A 3⟩

def ScaledRow.d (s : ScaledRow) := s.d0-s.κ
def ScaledRow.e (s : ScaledRow) := s.e0-s.κ*s.a
def ScaledRow.f (s : ScaledRow) := s.f0-s.κ*s.b

structure PointBounds (s : ScaledRow) (q u M β ε : ℝ) : Prop where
  aLo : 2+u+1.68*q+β*(2+u)-ε*q ≤ s.a
  aHi : s.a ≤ M*(2+u+1.72*q)+ε*q
  bLo : (1+u)*(1+u)/2+2.52*(1+u)*q+2*q*q+β*(1+u)*(1+u)-ε*q*q ≤ s.b
  bHi : s.b ≤ M^2*((1+u)*(1+u)/2+2.55*(1+u)*q+2.86*q*q)+ε*q*q
  dLo : 1+β-3*ε ≤ s.d0
  dHi : s.d0 ≤ 1+2*(M-1)-β+3*ε
  eLo : 1+u+3*q+2*β*(1+u)-2*ε*q ≤ s.e0
  eHi : s.e0 ≤ M^2*(1+u+3.54*q)+2*ε*q
  fLo : u*u/2+3.87*u*q+6*q*q-2*ε*q*q ≤ s.f0
  fHi : s.f0 ≤ M^3*(u*u/2+3.90*u*q+7.30*q*q)+2*ε*q*q
  cHi : s.c ≤ M^3*(u^3/6+1.7*u*u*q+4.84*u*q*q+3.89*q^3)+ε*q^3
  ratio : s.c/s.f0 ≤ M^3*(u+3*q)/3

theorem actual_point_bounds {j m : ℕ} (hj : 64≤j) :
    PointBounds (actualRow j m) (1/j) (m/j) (cMass j) (cBeta j) (cEta j) := by
  have jp : 0<(j:ℝ) := by exact_mod_cast (show 0<j by omega)
  obtain ⟨al,au,dl,du⟩ := true_linear_envelopes (m:=m) hj
  obtain ⟨bl,bu,el,eu⟩ := true_quadratic_envelopes (m:=m) hj
  obtain ⟨_,cu,fl,fu⟩ := true_cubic_envelopes (m:=m) hj
  obtain ⟨fpos,rel⟩ := relative_cubic (m:=m) hj
  dsimp only [actualRow]
  constructor
  · have z := div_le_div_of_nonneg_right al jp.le
    convert z using 1 <;> first | rfl | field_simp
  · have z := div_le_div_of_nonneg_right au jp.le
    convert z using 1 <;> first | rfl | field_simp
  · have z := div_le_div_of_nonneg_right bl (pow_nonneg jp.le 2)
    convert z using 1 <;> first | rfl | field_simp
  · have z := div_le_div_of_nonneg_right bu (pow_nonneg jp.le 2)
    convert z using 1 <;> first | rfl | field_simp
  · exact dl
  · exact du
  · have z := div_le_div_of_nonneg_right el jp.le
    convert z using 1 <;> first | rfl | field_simp
  · have z := div_le_div_of_nonneg_right eu jp.le
    convert z using 1 <;> first | rfl | field_simp
  · have z := div_le_div_of_nonneg_right fl (pow_nonneg jp.le 2)
    dsimp only [dvLower] at z
    convert z using 1 <;> first | rfl | field_simp
  · have z := div_le_div_of_nonneg_right fu (pow_nonneg jp.le 2)
    dsimp only [dvUpper] at z
    convert z using 1 <;> first | rfl | (field_simp; ring)
  · have z := div_le_div_of_nonneg_right cu (pow_nonneg jp.le 3)
    dsimp only [vUpper] at z
    convert z using 1 <;> first | rfl | field_simp
  · have z := div_le_div_of_nonneg_right rel jp.le
    convert z using 1 <;> first | rfl | field_simp

#print axioms actual_point_bounds
end OrderedPartitions.CubicChamber.Box
