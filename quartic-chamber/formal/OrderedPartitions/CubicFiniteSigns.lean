import OrderedPartitions.QuadraticExactSigns

/-! Integer pseudo-remainder certificates for the finite cubic range. -/

open Finset Polynomial

namespace OrderedPartitions.CubicFinite

open QuadraticExact

/-- Signed remainder of an upper quartic on division by an old cubic.
Its coefficients are scaled by the square of the old leading coefficient. -/
def separator {R : Type*} [Ring R] (a b c d e f g h k : R) : R × R × R :=
  let z := d*h-k*c
  (z*a-d*d*e, d*k*a+z*b-d*d*f, d*k*b+z*c-d*d*g)

/-- The lower-degree check can be applied to the separator and old row. -/
def signs {R : Type*} [Ring R] [LT R] (jump : Prop) (a b c d e f g h k : R) : Prop :=
  let r := separator a b c d e f g h k
  0 < e ∧ (0 < k ↔ jump) ∧ inequalities True r.1 r.2.1 r.2.2 a b c d

def integerSigns (j n : ℕ) (p q : Coefficients) (k : ℕ) : Prop :=
  signs (n+1=4*j) (p.constant : ℤ) (p.linear : ℤ) (p.quadratic : ℤ) (p.cubic : ℤ)
    (q.constant : ℤ) (q.linear : ℤ) (q.quadratic : ℤ) (q.cubic : ℤ) (k : ℤ)

instance (j n : ℕ) (p q : Coefficients) (k : ℕ) : Decidable (integerSigns j n p q k) := by
  unfold integerSigns signs inequalities
  infer_instance

/-- Re-use the shared four-column history. A fourth large block first appears at
size \(4j\), where the last block must have size \(j\). -/
def fourth (j n : ℕ) (history : List Coefficients) : ℕ :=
  if n = 4*j then binomial (4*j) j * (atSize (4*j) (3*j) history).cubic else 0

theorem fourth_count {j n : ℕ} (hj : 1 ≤ j) (hn : n ≤ 4*j) :
    fourth j n (rows j (4*j)) = count n j 4 := by
  unfold fourth
  split_ifs with heq
  · subst n
    have h := count_recurrence (4*j-1) hj 4
    rw [show 4*j-1+1 = 4*j by omega] at h
    have hc := atSize_eq (n := 3*j) (top := 4*j) (d := 3) hj (by omega) (by decide)
    change (atSize (4*j) (3*j) (rows j (4*j))).cubic = count (3*j) j 3 at hc
    rw [hc, binomial_eq (by omega : j ≤ 4*j), h, sum_eq_single j]
    · simp [show 4*j-j = 3*j by omega]
    · intro r hr hrj
      have hsize := mem_Icc.mp hr
      by_cases hlarge : j ≤ r
      · simp [hlarge, count_above_degree hj (by omega : 4*j-r < 3*j)]
      · simp [hlarge, count_above_degree hj (by omega : 4*j-r < 4*j)]
    · intro hj'
      exact (hj' (mem_Icc.mpr ⟨hj, by omega⟩)).elim
  · exact (count_above_degree hj (by omega)).symm

/-- Each cutoff is checked in one reduction of the shared last-block table. -/
def checkCutoff (j : ℕ) : Bool :=
  let top := 4*j
  let history := rows j top
  (List.range j).all fun m ↦
    let n := 3*j+m
    decide (integerSigns j n (atSize top n history) (atSize top (n+1) history)
      (fourth j (n+1) history))

def OriginalSigns (j n : ℕ) : Prop :=
  signs (n+1=4*j) ((row n j).coeff 0) ((row n j).coeff 1) ((row n j).coeff 2)
    ((row n j).coeff 3) ((row (n+1) j).coeff 0) ((row (n+1) j).coeff 1)
    ((row (n+1) j).coeff 2) ((row (n+1) j).coeff 3) ((row (n+1) j).coeff 4)

private theorem signs_cast {jump : Prop} {a b c d e f g h k : ℤ}
    (cert : signs jump a b c d e f g h k) :
    signs jump (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (e : ℝ) (f : ℝ)
      (g : ℝ) (h : ℝ) (k : ℝ) := by
  simp only [signs, separator, inequalities] at cert ⊢
  rcases cert with ⟨he, hk, hA, hB, hC, ha, hb, hc, hd, hu, hv⟩
  refine ⟨by exact_mod_cast he, ⟨fun hp ↦ hk.mp (by exact_mod_cast hp),
    fun hj ↦ by exact_mod_cast hk.mpr hj⟩, by exact_mod_cast hA, by exact_mod_cast hB,
    by exact_mod_cast hC, by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hc,
    iff_true_intro (by exact_mod_cast hd.mpr trivial), by exact_mod_cast hu,
    by exact_mod_cast hv⟩

theorem checkCutoff_sound {j n : ℕ} (hj : 1 ≤ j) (lo : 3*j ≤ n) (hi : n < 4*j)
    (passed : checkCutoff j = true) : OriginalSigns j n := by
  let p := atSize (4*j) n (rows j (4*j))
  let q := atSize (4*j) (n+1) (rows j (4*j))
  let k := fourth j (n+1) (rows j (4*j))
  let m := n-3*j
  have starts : 3*j+m=n := by omega
  have within : m < j := by omega
  have cert := List.all_eq_true.mp passed m (List.mem_range.mpr within)
  simp only [starts] at cert
  have checked : integerSigns j n p q k := of_decide_eq_true cert
  have hp (d : ℕ) (hd : d < 4) : (row n j).coeff d = (p.atDegree d : ℝ) := by
    rw [coeff_row hj, atSize_eq hj (by omega : n ≤ 4*j) hd]
  have hq (d : ℕ) (hd : d < 4) : (row (n+1) j).coeff d = (q.atDegree d : ℝ) := by
    rw [coeff_row hj, atSize_eq hj (by omega : n+1 ≤ 4*j) hd]
  have hk : (row (n+1) j).coeff 4 = (k : ℝ) := by
    rw [coeff_row hj, ← fourth_count hj (by omega : n+1 ≤ 4*j)]
  unfold OriginalSigns
  rw [hp 0 (by decide), hp 1 (by decide), hp 2 (by decide), hp 3 (by decide),
    hq 0 (by decide), hq 1 (by decide), hq 2 (by decide), hq 3 (by decide), hk]
  unfold integerSigns at checked
  simpa [Coefficients.atDegree] using signs_cast checked

#print axioms fourth_count
#print axioms checkCutoff_sound

end OrderedPartitions.CubicFinite
