import OrderedPartitions.QuadraticTransport
import OrderedPartitions.QuadraticRangeMargin

/-! The full quadratic chamber and the jump to a cubic for large thresholds. -/

noncomputable section
namespace OrderedPartitions.QuadraticOrder
open Kernel QuadraticRange

/-- The genuine adjacent row polynomials strictly interlace on the quadratic
platform, including its final transition to a cubic. -/
theorem original_quadratic_large {j m : ℕ} (hj : 50 ≤ j) (hm : m < j) :
    let n := 2*j+m
    Adjacent (row n j) (row (n+1) j) (n+1 = 3*j) := by
  let n := 2*j+m
  let a := normalizedMoment n j 1
  let b := normalizedMoment n j 2
  let c := normalizedMoment (n+1) j 3
  let da := normalizedMoment (n+1) j 1-a
  let db := normalizedMoment (n+1) j 2-b
  have jR : (50:ℝ) ≤ j := by exact_mod_cast hj
  have mR : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have mj : (m:ℝ) < j := by exact_mod_cast hm
  obtain ⟨al,au,dal,dau,bl,bu,dbl,dbu⟩ := original_quadratic_estimates hj m
  obtain ⟨cl,cu,edge⟩ := original_cubic_boundary hj hm
  have e : c = 0 ∨ (m:ℝ) = j-1 := edge.imp_right (fun h ↦ by
    have h' : m+1=j := by omega
    have eqR : (m:ℝ)+1=j := by exact_mod_cast h'
    linarith)
  have a0 : 0 ≤ a := le_trans (by positivity : (0:ℝ) ≤ (j:ℝ)+m) al
  have b0 : 0 < b := lt_of_lt_of_le (by positivity : 0 < 0.49*((m:ℝ)+1)*(m+2)) bl
  obtain ⟨sl,su,tl,tu⟩ := corrected_bounds (a:=a) (b:=b) (c:=c) (da:=da) (db:=db)
    jR mR a0 au bl cl cu e dal dau dbl dbu
  let S := da-c/b
  let T := db-c*a/b
  have s0 : 0 < S := lt_of_lt_of_le (by norm_num : (0:ℝ)<0.98) sl
  have t0 : 0 < T := lt_of_lt_of_le (by positivity : (0:ℝ)<(m:ℝ)+1.5) tl
  have neg := decisive_margin (S:=S) (T:=T) jR mR mj al bu b0.le sl su tl tu
  have sep : T/S+b*S/T < a := by
    field_simp [s0,t0]
    nlinarith only [neg]
  have roots := normalized_adjacent (a:=a) (δa:=da) (δb:=db) b0 cl s0 t0 sep
  apply original_adjacent_of_normalized (by omega) (show n<3*j by dsimp [n]; omega)
  simpa only [da,db,add_sub_cancel] using roots

#print axioms original_quadratic_large
end OrderedPartitions.QuadraticOrder
