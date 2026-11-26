import OrderedPartitions.CubicActualConditions
import OrderedPartitions.CubicChamberOriginal

noncomputable section
namespace OrderedPartitions.CubicChamber
open Kernel QuadraticOrder Box

/-- The actual pair at a large cutoff. The last rank in the chamber is the
cubic-to-quartic step, with a new smallest root. -/
theorem original_large_offset {j m : ℕ} (hj : 64≤j) (hm : m<j) :
    let n := 3*j+m
    CubicAdjacent (row n j) (row (n+1) j) (n+1=4*j) := by
  let n := 3*j+m
  let J : ℝ := j
  let a (i : ℕ) := normalizedMoment n j i
  let upper (i : ℕ) := normalizedMoment (n+1) j i
  let Δ (i : ℕ) := upper i-a i
  let k := upper 4/a 3
  let d := Δ 1-k
  let e := Δ 2-k*a 1
  let f := Δ 3-k*a 2
  let r := actualRow j m
  have hJ : 0<J := by dsimp [J];exact_mod_cast (show 0<j by omega)
  obtain ⟨V,ha,hb,hc,hd,he,hf,H,cap,near,far⟩ := actual_conditions hj hm
  have ra : r.a=a 1/J := rfl
  have rb : r.b=a 2/J^2 := rfl
  have rc : r.c=a 3/J^3 := rfl
  have rd : r.d=d := rfl
  have re : r.e=e/J := by dsimp [r,ScaledRow.e,actualRow,e,Δ,a,upper,n,k,J];ring
  have rf : r.f=f/J^2 := by dsimp [r,ScaledRow.f,actualRow,f,Δ,a,upper,n,k,J];ring
  change 0≤r.a at ha
  change 0<r.b at hb
  change 0<r.c at hc
  rw [ra] at ha
  rw [rb] at hb
  rw [rc] at hc
  change 0<r.e at he
  change 0<r.f at hf
  rw [re] at he
  rw [rf] at hf
  have a1 : 0≤a 1 := by simpa using (le_div_iff₀ hJ).mp ha
  have a2 := (div_pos_iff_of_pos_right (pow_pos hJ 2)).mp hb
  have a3 := (div_pos_iff_of_pos_right (pow_pos hJ 3)).mp hc
  have e0 := (div_pos_iff_of_pos_right hJ).mp he
  have f0 := (div_pos_iff_of_pos_right (pow_pos hJ 2)).mp hf
  obtain ⟨klo,_,before,entry⟩ := true_quartic_correction hj hm
  have kk : 0≤k := klo
  have kn : (0<k) ↔ n+1=4*j := by
    by_cases eqn : m+1=j
    · exact ⟨fun _ ↦ by dsimp [n];omega,fun _ ↦ div_pos (entry eqn) a3⟩
    · have zero : upper 4=0 := before (by omega)
      simp [k,zero,n,show 3*j+m+1≠4*j by omega]
  have result := normalized_chamber_from_scaled (a:=a 1) (b:=a 2) (c:=a 3) (d:=d) (e:=e)
    (f:=f) (k:=k) (V:=V) hJ a1 a2 a3 hd e0 f0 kk
    (by simpa only [← rd,← re,← rf] using H)
    (by simpa only [← rd,← re,← rf] using cap)
    (by simpa only [← ra,← rb,← rd,← re,← rf] using near)
    (by simpa only [← ra,← rb,← rc,← re,← rf] using far)
  have e1 : a 1+d+k=upper 1 := by dsimp [d,Δ]; ring
  have e2 : a 2+e+k*a 1=upper 2 := by dsimp [e,Δ]; ring
  have e3 : a 3+f+k*a 2=upper 3 := by dsimp [f,Δ]; ring
  have e4 : k*a 3=upper 4 := div_mul_cancel₀ _ a3.ne'
  rw [e1,e2,e3,e4,propext kn] at result
  exact original_cubic_chamber_of_normalized (by omega : 2≤j) (by dsimp [n];omega : n<4*j) result

theorem original_large {n j : ℕ} (hj : 64≤j) (lo : 3*j≤n) (hi : n<4*j) :
    CubicAdjacent (row n j) (row (n+1) j) (n+1=4*j) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le lo
  exact original_large_offset hj (by omega)

#print axioms original_large_offset
#print axioms original_large
end OrderedPartitions.CubicChamber
