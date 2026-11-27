import OrderedPartitions.HardRodWindowPoly
import OrderedPartitions.HardRodRightBrackets

noncomputable section
namespace OrderedPartitions.RootTracking
open Polynomial InterlacingStep Kernel

def rowSlope (j : ℕ) : ℝ := (j:ℝ)*markScale j

theorem rowSlope_pos {j : ℕ} (hj : 2≤j) : 0<rowSlope j :=
  mul_pos (by exact_mod_cast (show 0<j by omega)) (markScale_pos j)

def originalCoordinate (j : ℕ) (y : ℝ) := 1+y/rowSlope j

theorem originalCoordinate_mono {j : ℕ} (hj : 2≤j) : StrictMono (originalCoordinate j) :=
  by
    intro a b hab
    unfold originalCoordinate
    linarith [div_lt_div_of_pos_right hab (rowSlope_pos hj)]

theorem original_window_degree {M n j : ℕ} (hj : 2≤j) (cap : n<(M+1)*j) :
    (row n j).natDegree=(windowPoly M j n).natDegree := by
  have pos := original_eval_pos (by omega : 1≤j) n
  have eqn : row n j = C ((row n j).eval 1) *
      (windowPoly M j n).comp (C (rowSlope j)*(X-C 1)) := by
    apply Polynomial.funext
    intro t
    simpa only [eval_mul,eval_comp,eval_C,eval_sub,eval_X,rowSlope] using
      original_windowPoly (by omega : 1≤j) cap t
  rw [eqn,natDegree_C_mul pos.ne',natDegree_comp,natDegree_C_mul (rowSlope_pos hj).ne',
    natDegree_X_sub_C,mul_one]

theorem original_root_array {M j n d : ℕ} {xs : Fin d→ℝ} (hj : 2≤j)
    (cap : n<(M+1)*j) (h : RootArray (windowPoly M j n) xs) :
    RootArray (row n j) (originalCoordinate j ∘ xs) := by
  have j1 : 1≤j := by omega
  have roots (i : Fin d) : (row n j).eval (originalCoordinate j (xs i))=0 := by
    rw [original_windowPoly j1 cap]
    change _ * (windowPoly M j n).eval (rowSlope j*(1+xs i/rowSlope j-1))=0
    rw [show rowSlope j*(1+xs i/rowSlope j-1)=xs i by field_simp [(rowSlope_pos hj).ne']; ring,
      h.zeros i,mul_zero]
  refine ⟨(originalCoordinate_mono hj).comp h.ordered,?_,?_,(original_window_degree hj cap).trans h.degree,roots⟩
  · intro i
    by_contra! hpos
    exact (QuadraticOrder.original_positive hj n hpos).ne' (roots i)
  · intro hz
    have pos := original_eval_pos j1 n
    simp [hz] at pos

theorem original_ordered_pair {d M j n : ℕ} (hj : 2≤j) (cap : n+1<(M+1)*j)
    (h : OrderedPair d (windowPoly M j n) (windowPoly M j (n+1))) :
    OrderedPair d (row n j) (row (n+1) j) := by
  obtain ⟨xs,hp,stay|rise⟩ := h
  · obtain ⟨zs,hq,hz⟩ := stay
    exact ⟨_,original_root_array hj (by omega) hp,Or.inl ⟨_,original_root_array hj cap hq,
      fun i ↦ originalCoordinate_mono hj (hz.1 i),fun i k hik ↦ originalCoordinate_mono hj (hz.2 i k hik)⟩⟩
  · obtain ⟨zs,hq,hz⟩ := rise
    exact ⟨_,original_root_array hj (by omega) hp,Or.inr ⟨_,original_root_array hj cap hq,
      fun i ↦ ⟨originalCoordinate_mono hj (hz i).1,originalCoordinate_mono hj (hz i).2⟩⟩⟩
#print axioms original_window_degree
#print axioms original_root_array
#print axioms original_ordered_pair
end OrderedPartitions.RootTracking
