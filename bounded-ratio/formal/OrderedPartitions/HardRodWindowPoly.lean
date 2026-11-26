import OrderedPartitions.HardRodAllRanks
import OrderedPartitions.CubicChamberOriginal
import OrderedPartitions.HardRodDegree

noncomputable section
open Filter Polynomial Finset
open scoped Topology
namespace OrderedPartitions.Kernel

def windowPoly (M j n : ℕ) : ℝ[X] :=
  ∑ h ∈ range (M+1), Polynomial.monomial h (windowCoeff j n h)

theorem windowPoly_coeff (M j n h : ℕ) :
    (windowPoly M j n).coeff h = if h≤M then windowCoeff j n h else 0 := by
  simp [windowPoly,finsetSum_coeff,coeff_monomial,mem_range]

theorem windowPoly_eval (M j n : ℕ) (y : ℝ) :
    (windowPoly M j n).eval y = ∑ h ∈ range (M+1), windowCoeff j n h * y^h := by
  simp [windowPoly,eval_finsetSum,eval_monomial]

theorem original_windowPoly {M j n : ℕ} (hj : 1≤j) (hn : n<(M+1)*j) (t : ℝ) :
    (row n j).eval t = (row n j).eval 1 * (windowPoly M j n).eval ((j:ℝ)*markScale j*(t-1)) := by
  rw [original_normalized_sum hj hn t,windowPoly_eval]
  congr 1
  apply sum_congr rfl
  intro h _
  have nz : (j:ℝ)≠0 := by exact_mod_cast (show j≠0 by omega)
  simp only [windowCoeff,mul_pow]
  field_simp

private theorem const_window {j : ℕ} (hj : 1≤j) (n : ℕ) : windowCoeff j n 0=1 := by
  simp [windowCoeff,normalizedMoment,markedCount_zero,(original_eval_pos hj n).ne']

def speedPoly (M j n : ℕ) : ℝ[X] := C (j:ℝ)*(windowPoly M j (n+1)-windowPoly M j n)

theorem speedPoly_eval (M j n : ℕ) (hj : 1≤j) (y : ℝ) :
    (speedPoly (M+1) j n).eval y = ∑ h ∈ range (M+1), windowSpeed j n (h+1)*y^(h+1) := by
  simp only [speedPoly,eval_mul,eval_C,eval_sub,windowPoly_eval]
  rw [← sum_sub_distrib,mul_sum,sum_range_succ']
  simp only [const_window hj,pow_zero,mul_one,sub_self,mul_zero,add_zero]
  apply sum_congr rfl
  intro h _
  unfold windowSpeed
  ring

theorem original_moving_limits {J N : ℕ → ℕ} {Y : ℕ → ℝ} {x y : ℝ}
    (hx : 1<x) (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun i ↦ (N i:ℝ)/(J i:ℝ)) atTop (𝓝 x))
    (hy : Tendsto Y atTop (𝓝 y)) (M : ℕ) :
    Tendsto (fun i ↦ (windowPoly (M+1) (J i) (N i)).eval (Y i)) atTop (𝓝 ((HardRod.phi (M+1) x).eval y)) ∧
    Tendsto (fun i ↦ (speedPoly (M+1) (J i) (N i)).eval (Y i)) atTop (𝓝 (y*(HardRod.phi M (x-1)).eval y)) := by
  constructor
  · simp only [windowPoly_eval,HardRod.phi_eval]
    exact tendsto_finsetSum _ (fun h _ ↦ (window_coeff_limit hx hj hn h).mul (hy.pow h))
  · have t := tendsto_finsetSum (range (M+1)) (fun h _ ↦ (window_speed_limit hx hj hn h).mul (hy.pow (h+1)))
    have eqn : y*(HardRod.phi M (x-1)).eval y =
        ∑ h ∈ range (M+1), HardRod.rodCoeff h (x-1)*y^(h+1) := by
      rw [HardRod.phi_eval,mul_sum]
      apply sum_congr rfl
      intro h _
      rw [pow_succ];ring
    rw [eqn]
    apply t.congr'
    filter_upwards [hj.eventually_ge_atTop 1] with i hi
    exact (speedPoly_eval M (J i) (N i) hi (Y i)).symm

#print axioms original_windowPoly
#print axioms original_moving_limits
end OrderedPartitions.Kernel
