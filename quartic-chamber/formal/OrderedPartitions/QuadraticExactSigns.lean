import OrderedPartitions.QuadraticExactRows

/-! Exact signed remainders of the original quadratic row and its successor. -/

open Polynomial

namespace OrderedPartitions.QuadraticExact

/-- The signed linear remainder and the quadratic's value at its zero, after clearing
denominators. The upper row gains its cubic term exactly at the last step. -/
def inequalities {R : Type*} [Ring R] [LT R] (jump : Prop) (a b c d e f g : R) : Prop :=
  let u := c*c*e-c*g*a-(c*f-g*b)*b
  let v := c*c*d-(c*f-g*b)*a
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
    (0 < g ↔ jump) ∧ u < 0 ∧ a*u^2-b*u*v+c*v^2 < 0

def intInequalities (j n : ℕ) (p q : Coefficients) : Prop :=
  inequalities (n+1 = 3*j) (p.constant : ℤ) (p.linear : ℤ) (p.quadratic : ℤ)
    (q.constant : ℤ) (q.linear : ℤ) (q.quadratic : ℤ) (q.cubic : ℤ)

instance (j n : ℕ) (p q : Coefficients) : Decidable (intInequalities j n p q) := by
  unfold intInequalities inequalities
  infer_instance

/-- The inequalities in the finite certificate, written directly on the two original rows. -/
def OriginalSigns (j n : ℕ) : Prop :=
  inequalities (n+1 = 3*j) ((row n j).coeff 0) ((row n j).coeff 1) ((row n j).coeff 2)
    ((row (n+1) j).coeff 0) ((row (n+1) j).coeff 1) ((row (n+1) j).coeff 2)
    ((row (n+1) j).coeff 3)

private theorem inequalities_intCast {jump : Prop} {a b c d e f g : ℤ}
    (h : inequalities jump a b c d e f g) :
    inequalities jump (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (e : ℝ) (f : ℝ) (g : ℝ) := by
  unfold inequalities at h ⊢
  rcases h with ⟨ha, hb, hc, hd, he, hf, hg, hu, hv⟩
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hc,
    by exact_mod_cast hd, by exact_mod_cast he, by exact_mod_cast hf,
    ⟨fun hpos ↦ hg.mp (by exact_mod_cast hpos), fun hjump ↦ by exact_mod_cast hg.mpr hjump⟩,
    by exact_mod_cast hu, by exact_mod_cast hv⟩

/-- Extract a given rank from a decreasing-size history. -/
def atSize (top n : ℕ) (history : List Coefficients) : Coefficients :=
  history[top-n]?.getD zeroRow

theorem atSize_eq {j top n d : ℕ} (hj : 1 ≤ j) (hn : n ≤ top) (hd : d < 4) :
    (atSize top n (rows j top)).atDegree d = count n j d := by
  simpa only [atSize, show top-(top-n) = n by omega] using
    rows_eq hj top (top-n) d (Nat.sub_le _ _) hd

/-- Test all the adjacent pairs in the quadratic range for one cutoff. -/
def checkCutoff (j : ℕ) : Bool :=
  let top := 3*j
  let history := rows j top
  (List.range j).all fun m ↦
    let n := 2*j+m
    decide (intInequalities j n (atSize top n history) (atSize top (n+1) history))

theorem checkCutoff_sound {j n : ℕ} (hj : 1 ≤ j) (lo : 2*j ≤ n) (hi : n < 3*j)
    (h : checkCutoff j = true) : OriginalSigns j n := by
  let p := atSize (3*j) n (rows j (3*j))
  let q := atSize (3*j) (n+1) (rows j (3*j))
  let m := n-2*j
  have hm : m < j := by omega
  have hn : 2*j+m = n := by omega
  have accepted := List.all_eq_true.mp h m (List.mem_range.mpr hm)
  simp only [hn] at accepted
  have stable : intInequalities j n p q := of_decide_eq_true accepted
  have hcoeff (d : ℕ) (hd : d < 4) : (row n j).coeff d = (p.atDegree d : ℝ) := by
    rw [coeff_row hj, atSize_eq hj (by omega : n ≤ 3*j) hd]
  have hcoeff' (d : ℕ) (hd : d < 4) : (row (n+1) j).coeff d = (q.atDegree d : ℝ) := by
    rw [coeff_row hj, atSize_eq hj (by omega : n+1 ≤ 3*j) hd]
  unfold OriginalSigns
  rw [hcoeff 0 (by decide), hcoeff 1 (by decide), hcoeff 2 (by decide),
    hcoeff' 0 (by decide), hcoeff' 1 (by decide), hcoeff' 2 (by decide), hcoeff' 3 (by decide)]
  simpa [Coefficients.atDegree] using inequalities_intCast stable

#print axioms checkCutoff_sound

end OrderedPartitions.QuadraticExact
