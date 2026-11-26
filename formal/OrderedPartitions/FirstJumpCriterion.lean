import OrderedPartitions.FirstJumpRows
import OrderedPartitions.QuadraticBracketing
import Mathlib.Algebra.Polynomial.Derivative

/-! The factorial-moment inequality expressed on the original labeled ordered partitions. -/

noncomputable section
open Polynomial

namespace OrderedPartitions

/-- The mean of the marked count under the uniform measure on the objects of a row. -/
def markedMean (p : ℝ[X]) : ℝ := p.derivative.eval 1 / p.eval 1

/-- At the first degree jump the moment inequality is necessary and sufficient for
a simple linear zero strictly between two distinct negative zeros of the true next row.
The last identity factors the entire next row. -/
theorem original_first_jump_iff {j : ℕ} (hj : 2 ≤ j) :
    let p := row (2*j-1) j
    let q := row (2*j) j
    q.coeff 2 / q.eval 1 < markedMean p * (markedMean q - markedMean p) ↔
      ∃ l m r : ℝ, l < m ∧ m < r ∧ r < 0 ∧ p.IsRoot m ∧
        ∀ x : ℝ, q.eval x = q.coeff 2 * (x-l) * (x-r) := by
  let u := (count (2*j-1) j 0 : ℝ)
  let v := (count (2*j-1) j 1 : ℝ)
  let a := (count (2*j) j 0 : ℝ)
  let b := (count (2*j) j 1 : ℝ)
  let c := (Nat.choose (2*j) j : ℝ)
  have hu : 0 < u := by
    dsimp [u]
    exact_mod_cast count_zero_positive (2*j-1) hj
  have hv : 0 < v := by
    dsimp [v]
    exact_mod_cast count_one_positive (j := j) (by omega) (by omega : j ≤ 2*j-1)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast count_zero_positive (2*j) hj
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast count_one_positive (j := j) (by omega) (by omega : j ≤ 2*j)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Nat.choose_pos (by omega : j ≤ 2*j)
  let p := row (2*j-1) j
  let q := row (2*j) j
  have hp : p = C u + C v * X := row_linear hj (by omega)
  have hq : q = C a + C b * X + C c * X^2 := row_first_jump hj
  have hqc : q.coeff 2 = c := by
    dsimp [q,c]
    rw [coeff_row (by omega : 1 ≤ j), first_jump_count (by omega : 1 ≤ j)]
  have pe (x : ℝ) : p.eval x = u + v*x := by simp [hp]
  have qe (x : ℝ) : q.eval x = a + b*x + c*x^2 := by simp [hq]
  have pm : markedMean p = v/(u+v) := by simp [markedMean,hp]
  have qm : markedMean q = (b+2*c)/(a+b+c) := by simp [markedMean,hq]; ring
  change q.coeff 2 / q.eval 1 < markedMean p * (markedMean q - markedMean p) ↔ _
  rw [hqc, pm, qm, qe]
  simp only [one_pow, mul_one]
  rw [moment_gap_iff u v a b c hu hv ha hb hc, first_jump_brackets_iff u v a b c hu hv ha hc]
  constructor
  · rintro ⟨l,r,hl,hr,hr0,hfac⟩
    refine ⟨l,-u/v,r,hl,hr,hr0,?_,?_⟩
    · change p.eval (-u/v) = 0
      rw [pe]
      field_simp
      ring
    · intro x
      change q.eval x = c*(x-l)*(x-r)
      rw [qe, hfac]
  · rintro ⟨l,m,r,hl,hr,hr0,hm,hfac⟩
    change p.eval m = 0 at hm
    rw [pe] at hm
    have hm' : m = -u/v := (eq_div_iff hv.ne').mpr (by linarith)
    subst m
    exact ⟨l,r,hl,hr,hr0,fun x ↦ (qe x).symm.trans (hfac x)⟩

#print axioms original_first_jump_iff
end OrderedPartitions
