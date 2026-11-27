import OrderedPartitions.HardRodEscape
import Mathlib.Order.Filter.Finite

/-! Transfer the reciprocal root test to polynomials with converging coefficients. -/

open Polynomial Filter
open scoped Topology

namespace OrderedPartitions.HardRod

private theorem finite_coeff_bounds {ι : Type*} {l : Filter ι} {d : ℕ}
    {f : ι → ℕ → ℝ} {a : ℕ → ℝ}
    (conv : ∀ k < d, Tendsto (fun i ↦ f i k) l (𝓝 (a k))) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ᶠ i in l, ∀ k < d, |f i k| ≤ M) := by
  let M := 1 + ∑ k ∈ Finset.range d, |a k|
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  have all : ∀ᶠ i in l, ∀ k ∈ Finset.range d, |f i k| ≤ M := by
    apply (eventually_all_finset _).mpr
    intro k hk
    have lim : |a k| < M := by
      have b := Finset.single_le_sum (f := fun z ↦ |a z|) (fun z _ ↦ abs_nonneg _) hk
      dsimp [M]
      linarith only [b]
    exact (((conv k (Finset.mem_range.mp hk)).abs.eventually_lt tendsto_const_nhds lim).mono
      (fun _ h ↦ h.le))
  exact all.mono (fun _ h k hk ↦ h k (Finset.mem_range.mpr hk))

/-- A small old leading coefficient creates a root that lies eventually to
the left of every prescribed threshold. The inequality on the top coefficient
is relative, whereas convergence of the scaled lower differences suffices.
This result makes no assumptions about roots already found in bounded regions. -/
theorem eventually_escape_of_growth {ι : Type*} {l : Filter ι}
    {p q : ι → ℝ[X]} {scale lag : ι → ℝ} {d : ℕ} (hd : 1 ≤ d)
    {oldLimits diffLimits : ℕ → ℝ}
    (next_pos : 0 < oldLimits (d-1))
    (lead : Tendsto (fun i ↦ (p i).coeff d) l (𝓝 0))
    (old_lower : ∀ k < d, Tendsto (fun i ↦ (p i).coeff k) l (𝓝 (oldLimits k)))
    (diff_lower : ∀ k < d,
      Tendsto (fun i ↦ scale i*((q i).coeff k-(p i).coeff k)) l (𝓝 (diffLimits k)))
    (degrees : ∀ᶠ i in l, (p i).natDegree ≤ d ∧ (q i).natDegree ≤ d)
    (positive : ∀ᶠ i in l, 0 < (p i).coeff d ∧ 0 < scale i ∧ 0 < lag i)
    (growth : ∀ᶠ i in l, (p i).coeff d ≤ lag i*((q i).coeff d-(p i).coeff d))
    (small_ratio : Tendsto (fun i ↦ lag i/scale i) l (𝓝 0))
    (threshold : ℝ) :
    ∀ᶠ i in l, ∃ r : ℝ, r < threshold ∧ (p i).IsRoot r ∧ 0 < (-1)^d*(q i).eval r := by
  obtain ⟨M, Mn, old_bound⟩ := finite_coeff_bounds old_lower
  obtain ⟨N, Nn, diff_bound⟩ := finite_coeff_bounds diff_lower
  have next := old_lower (d-1) (by omega)
  have next_positive : ∀ᶠ i in l, 0 < (p i).coeff (d-1) :=
    tendsto_const_nhds.eventually_lt next next_pos
  have wide : ∀ᶠ i in l, 2*(p i).coeff d < (p i).coeff (d-1) :=
    (lead.const_mul 2).eventually_lt next (by simp [next_pos])
  have quadratic : ∀ᶠ i in l, 4*(p i).coeff d*(((d:ℝ)+1)*M) < ((p i).coeff (d-1))^2 :=
    ((lead.const_mul 4).mul_const (((d:ℝ)+1)*M)).eventually_lt (next.pow 2)
      (by simpa using sq_pos_of_pos next_pos)
  have relative : ∀ᶠ i in l, 2*(((d:ℝ)+1)*N)*(lag i/scale i) < (p i).coeff (d-1) :=
    (small_ratio.const_mul (2*(((d:ℝ)+1)*N))).eventually_lt next (by simp [next_pos])
  have far : ∀ᶠ i in l, (-2*threshold)*(p i).coeff d < (p i).coeff (d-1) :=
    (lead.const_mul (-2*threshold)).eventually_lt next (by simp [next_pos])
  filter_upwards [degrees, positive, growth, old_bound, diff_bound, next_positive, wide,
    quadratic, relative, far] with i deg pos gr old_bd diff_bd bp wide_i quad rel far_i
  have small : 2*(p i).coeff d/(p i).coeff (d-1) ≤ 1 :=
    (div_le_iff₀ bp).mpr (by simpa only [one_mul] using wide_i.le)
  have new_bd (k : ℕ) (hk : k < d) : |(q i).coeff k-(p i).coeff k| ≤ N/scale i := by
    have cap := diff_bd k hk
    rw [abs_mul, abs_of_pos pos.2.1, mul_comm] at cap
    exact (le_div_iff₀ pos.2.1).mpr cap
  have new_budget :
      2*(p i).coeff d*(((d:ℝ)+1)*(N/scale i)) <
        (p i).coeff (d-1)*((q i).coeff d-(p i).coeff d) := by
    apply (mul_lt_mul_iff_of_pos_right pos.2.2).mp
    calc
      _ = (p i).coeff d*(2*(((d:ℝ)+1)*N)*(lag i/scale i)) := by ring
      _ < (p i).coeff d*(p i).coeff (d-1) := mul_lt_mul_of_pos_left rel pos.1
      _ ≤ _ := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right gr bp.le
  obtain ⟨r, hr, hroot, sign⟩ := escape_of_coefficient_bounds hd deg.1 deg.2 Mn
    (div_nonneg Nn pos.2.1.le) pos.1 bp small quad new_budget old_bd new_bd
  have below : -((p i).coeff (d-1)/(2*(p i).coeff d)) < threshold := by
    rw [← neg_div]
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) pos.1)).mpr
    nlinarith only [far_i]
  exact ⟨r, hr.trans below, hroot, sign⟩

#print axioms eventually_escape_of_growth

end OrderedPartitions.HardRod
