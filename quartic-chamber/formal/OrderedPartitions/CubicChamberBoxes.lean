import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

/-! The exact rational grid and endpoint tests for the cubic chamber. -/

namespace OrderedPartitions.CubicChamber.Box

/-- One cell of the 6-by-128 grid, with the flag for a quartic entry. -/
structure Cell where
  iq : Fin 6
  iu : Fin 128
  jump : Bool

def Cell.qLo (c : Cell) : ℚ := (c.iq.val : ℚ) / (64*6)
def Cell.qHi (c : Cell) : ℚ := ((c.iq.val : ℚ)+1) / (64*6)
def Cell.uLo (c : Cell) : ℚ := (c.iu.val : ℚ) / 128
def Cell.uHi (c : Cell) : ℚ := ((c.iu.val : ℚ)+1) / 128

/-- A quartic entry can occur only in cells that meet the line u+q=1. -/
def Cell.Valid (c : Cell) : Prop :=
  c.jump = true → c.uLo ≤ 1-c.qLo ∧ 1-c.qHi ≤ c.uHi

instance (c : Cell) : Decidable c.Valid := by
  unfold Cell.Valid
  infer_instance

def beta (q : ℚ) : ℚ := (69/100)*q/(1+q)
def mass (r : ℚ) : ℚ := 1/(1-(7/10)*r)
def eta (r : ℚ) : ℚ := r/100

/-- The endpoint bounds are in the dimensionless units of the chamber proof. -/
structure Bounds where
  aLower : ℚ
  aUpper : ℚ
  bLower : ℚ
  bUpper : ℚ
  dLower : ℚ
  dUpper : ℚ
  eLower : ℚ
  eUpper : ℚ
  fLower : ℚ
  fUpper : ℚ
  ratioUpper : ℚ

/-- Use the lower endpoints for increasing lower terms and upper endpoints for costs.
The quartic correction is subtracted from the three lower difference coefficients. -/
def Cell.bounds (cell : Cell) : Bounds :=
  let q := cell.qLo
  let r := cell.qHi
  let u := cell.uLo
  let v := cell.uHi
  let s := 1+u
  let t := 1+v
  let β := beta q
  let M := mass r
  let ε := eta r
  let correction := if cell.jump then 50*r^3 else 0
  let A := M*(2+v+(172/100)*r)+ε*r
  let B := M^2*(t*t/2+(255/100)*t*r+(286/100)*r*r)+ε*r*r
  let F := u*u/2+(387/100)*u*q+6*q*q-2*ε*r*r-correction*B
  let C := M^3*(v^3/6+(17/10)*v*v*r+(484/100)*v*r*r+(389/100)*r^3)+ε*r^3
  {
    aLower := 2+u+(168/100)*q+β*(2+u)-ε*r
    aUpper := A
    bLower := s*s/2+(252/100)*s*q+2*q*q+β*s*s-ε*r*r
    bUpper := B
    dLower := 1+β-3*ε-correction
    dUpper := 1+2*(M-1)+3*ε-β
    eLower := s+3*q+2*β*s-2*ε*r-correction*A
    eUpper := M^2*(t+(354/100)*r)+2*ε*r
    fLower := F
    fUpper := M^3*(v*v/2+(390/100)*v*r+(730/100)*r*r)+2*ε*r*r
    ratioUpper := if cell.jump then C/F else M^3*(v+3*r)/3
  }

/-- The upper enclosure of the scaled quadratic capacity d*f/e². -/
def Bounds.capacity (b : Bounds) : ℚ := b.dUpper*b.fUpper/b.eLower^2

/-- Five successive rational upper bounds are obtained by the fixed-point iteration. -/
def upperAt (h : ℚ) : ℕ → ℚ
  | 0 => 5/4
  | k+1 => 1/(1-h*upperAt h k)

def Bounds.finalUpper (b : Bounds) : ℚ := upperAt b.capacity 5

def Bounds.gap (b : Bounds) : ℚ := b.aLower*b.dLower-b.eUpper

def Bounds.nearMargin (b : Bounds) : ℚ :=
  b.gap*b.eLower-b.finalUpper*b.dUpper*max 0 (b.bUpper*b.dUpper-b.fLower)

def Bounds.farMargin (b : Bounds) : ℚ :=
  1-b.finalUpper*b.aUpper*b.fUpper/(b.bLower*b.eLower)-b.ratioUpper*b.eUpper/b.bLower

/-- The four strict margins and the denominators used by the arithmetic certificate. -/
def Cell.Passes (cell : Cell) : Prop :=
  let b := cell.bounds
  0 < b.aLower ∧ 0 < b.bLower ∧ 0 < b.dLower ∧ 0 < b.eLower ∧ 0 < b.dUpper ∧
    0 < b.eUpper ∧ 0 < b.fUpper ∧ (cell.jump = true → 0 < b.fLower) ∧
    0 ≤ b.capacity ∧ 21/1000 < 4/25-b.capacity ∧
    (∀ k : Fin 5, b.capacity*upperAt b.capacity k.val < 1) ∧
    964/1000 < b.gap ∧ 35/1000 < b.nearMargin ∧ 136/1000 < b.farMargin

instance (cell : Cell) : Decidable cell.Passes := by
  unfold Cell.Passes
  infer_instance

/-- The cell list includes every ordinary cell and the possible quartic cells. -/
def allCells (jump : Bool) : List Cell :=
  ((List.finRange 6).flatMap (fun iq ↦ (List.finRange 128).map fun iu ↦ ⟨iq, iu, jump⟩)).filter
    (fun cell ↦ decide cell.Valid)

/-- The actual dimensionless coefficients meet the endpoint bounds of the cell. -/
structure Encloses (cell : Cell) (a b c d e f : ℝ) : Prop where
  aLower : (cell.bounds.aLower : ℝ) ≤ a
  aUpper : a ≤ (cell.bounds.aUpper : ℝ)
  bLower : (cell.bounds.bLower : ℝ) ≤ b
  bUpper : b ≤ (cell.bounds.bUpper : ℝ)
  cNonneg : 0 ≤ c
  dLower : (cell.bounds.dLower : ℝ) ≤ d
  dUpper : d ≤ (cell.bounds.dUpper : ℝ)
  eLower : (cell.bounds.eLower : ℝ) ≤ e
  eUpper : e ≤ (cell.bounds.eUpper : ℝ)
  fPositive : 0 < f
  fLower : (cell.bounds.fLower : ℝ) ≤ f
  fUpper : f ≤ (cell.bounds.fUpper : ℝ)
  ratio : c/f ≤ (cell.bounds.ratioUpper : ℝ)

end OrderedPartitions.CubicChamber.Box
