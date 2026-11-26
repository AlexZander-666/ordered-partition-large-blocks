import OrderedPartitions.RenewalOriginal
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Antidiag.Prod

noncomputable section
open Finset PowerSeries
namespace OrderedPartitions.Renewal

def q (rho : ℝ) (n : ℕ) : ℝ := rho^n/n.factorial

theorem q_hasSum (rho : ℝ) : HasSum (q rho) (Real.exp rho) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp rho

theorem geom_coeff (n : ℕ) : coeff n geom = 1 := by simp [geom]

theorem coeff_mul_geom (S : PowerSeries ℝ) (n : ℕ) :
    coeff n (S*geom) = ∑ i ∈ range (n+1), coeff i S := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [geom_coeff]

theorem factorB_tail {rho : ℝ} (hr : Real.exp rho = 2) (n : ℕ) :
    coeff n (factorB rho) = ∑' k, q rho (k+(n+1)) := by
  rw [factorB, sub_mul, map_sub, show (2 : PowerSeries ℝ)*geom=geom+geom by ring, map_add,
    geom_coeff, coeff_mul_geom]
  simp only [coeff_rescale, PowerSeries.coeff_exp, map_div₀, map_one, map_natCast,
    mul_one_div]
  have eqn := (q_hasSum rho).summable.sum_add_tsum_nat_add (n+1)
  rw [(q_hasSum rho).tsum_eq, hr] at eqn
  change 1+1-(∑ i ∈ range (n+1), q rho i) = _
  linarith

private theorem q_diagonal (rho : ℝ) (n : ℕ) :
    ((n+1 : ℕ) : ℝ)*q rho (n+1) = rho*q rho n := by
  simp [q, pow_succ, Nat.factorial_succ]
  field_simp

private theorem b_double_sum {rho : ℝ} (hr : 0 ≤ rho) :
    HasSum (fun n ↦ ∑' k, q rho (k+(n+1))) (rho * Real.exp rho) := by
  let f (v : ℕ × ℕ) := q rho (v.1+v.2+1)
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have regroup (n : ℕ) :
      (∑' v : ↥(antidiagonal n), f (e ⟨n,v⟩)) = rho*q rho n := by
    rw [tsum_fintype]
    simp only [e, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, f]
    simp_rw [mem_antidiagonal.mp (Subtype.property _)]
    simpa using q_diagonal rho n
  have hf : Summable (fun v ↦ f (e v)) := by
    apply (summable_sigma_of_nonneg (fun v ↦ show 0 ≤ f (e v) by dsimp [f,q]; positivity)).mpr
    refine ⟨fun _ ↦ (hasSum_fintype _).summable, ?_⟩
    simpa only [regroup] using (q_hasSum rho).summable.mul_left rho
  have hp : Summable f := e.summable_iff.mp hf
  have hpval : ∑' v, f v = rho*Real.exp rho := by
    rw [← e.tsum_eq f, hf.tsum_sigma]
    simp_rw [regroup]
    exact ((q_hasSum rho).mul_left rho).tsum_eq
  have hpp := hp.tsum_prod
  rw [hpval] at hpp
  have hals := hp.prod.hasSum
  rw [← hpp] at hals
  simpa [f, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hals

theorem b_hasSum {rho : ℝ} (hr : Real.exp rho = 2) (hpos : 0 ≤ rho) :
    HasSum (fun n ↦ coeff n (factorB rho)) (2*rho) := by
  simp_rw [factorB_tail hr]
  simpa [hr, mul_comm] using b_double_sum hpos

theorem forcingJ_tail {rho : ℝ} (hr : Real.exp rho = 2) (hpos : 0 ≤ rho) (n : ℕ) :
    coeff n (forcingJ rho) = ∑' k, coeff (k+(n+1)) (factorB rho) := by
  rw [forcingJ, sub_mul, map_sub, coeff_C_mul, geom_coeff, mul_one, coeff_mul_geom]
  have h := b_hasSum hr hpos
  have eqn := h.summable.sum_add_tsum_nat_add (n+1)
  rw [h.tsum_eq] at eqn
  linarith

#print axioms factorB_tail
#print axioms b_hasSum
#print axioms forcingJ_tail

end OrderedPartitions.Renewal
