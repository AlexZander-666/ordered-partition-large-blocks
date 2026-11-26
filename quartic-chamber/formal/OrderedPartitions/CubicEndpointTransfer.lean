import OrderedPartitions.CubicScaledEnvelopes
import OrderedPartitions.CubicChamberBoxCoverage
import OrderedPartitions.CubicChamberBoxNumeric

noncomputable section
namespace OrderedPartitions.CubicChamber.Box
open OrderedPartitions.Kernel

def Cell.correction (cell : Cell) : ℚ := if cell.jump then 50*cell.qHi^3 else 0

def Cell.cUpper (cell : Cell) : ℚ :=
  let M := mass cell.qHi
  let v := cell.uHi
  let r := cell.qHi
  M^3*(v^3/6+(17/10)*v*v*r+(484/100)*v*r*r+(389/100)*r^3)+eta r*r^3

theorem endpoints_transport (cell : Cell) (s : ScaledRow) {q u M β ε : ℝ}
    (point : PointBounds s q u M β ε) (inc : cell.Contains q u)
    (q0 : 0≤q) (u0 : 0≤u) (M0 : 0≤M) (β0 : 0≤β) (ε0 : 0≤ε)
    (mh : M≤(mass cell.qHi : ℝ)) (bh : (beta cell.qLo : ℝ)≤β) (eh : ε≤(eta cell.qHi : ℝ))
    (az : 0≤s.a) (bz : 0≤s.b) (cz : 0≤s.c) (fz : 0<s.f0)
    (klo : 0≤s.κ) (khi : s.κ≤(cell.correction : ℝ)) (valid : cell.Valid) :
    Encloses cell s.a s.b s.c s.d s.e s.f := by
  obtain ⟨ql,qh,ul,uh⟩ := inc
  have ql0 : 0≤(cell.qLo : ℝ) := by unfold Cell.qLo; positivity
  have ul0 : 0≤(cell.uLo : ℝ) := by unfold Cell.uLo; positivity
  have b0 : 0≤(beta cell.qLo : ℝ) := by unfold beta; push_cast; positivity
  have mpos := M0.trans mh
  have epos := ε0.trans eh
  have vpos := u0.trans uh
  have rpos := q0.trans qh
  let A := (cell.bounds.aUpper : ℝ)
  let B := (cell.bounds.bUpper : ℝ)
  let C := (cell.cUpper : ℝ)
  let K := (cell.correction : ℝ)
  have al : (cell.bounds.aLower : ℝ)≤s.a := by
    apply le_trans _ point.aLo
    dsimp only [Cell.bounds]; push_cast
    gcongr ; first | positivity | norm_num
  have au : s.a≤A := by
    apply point.aHi.trans
    dsimp only [A,Cell.bounds]; push_cast
    gcongr ; first | positivity | norm_num
  have bl : (cell.bounds.bLower : ℝ)≤s.b := by
    apply le_trans _ point.bLo
    dsimp only [Cell.bounds]; push_cast
    gcongr ; first | positivity | norm_num
  have bu : s.b≤B := by
    apply point.bHi.trans
    dsimp only [B,Cell.bounds]; push_cast
    gcongr <;> first | positivity | norm_num
  have cu : s.c≤C := by
    apply point.cHi.trans
    dsimp only [C,Cell.cUpper]; push_cast
    gcongr <;> first | positivity | norm_num
  have kl : s.κ≤K := khi
  have ka := mul_le_mul kl au az (klo.trans kl)
  have kb := mul_le_mul kl bu bz (klo.trans kl)
  have dl : (cell.bounds.dLower : ℝ)≤s.d := by
    change ↑((1+beta cell.qLo-3*eta cell.qHi)-cell.correction)≤s.d0-s.κ
    push_cast; linarith only [point.dLo,bh,eh,khi]
  have du : s.d≤(cell.bounds.dUpper : ℝ) := by
    dsimp only [ScaledRow.d,Cell.bounds]; push_cast
    linarith only [point.dHi,klo,bh,eh,mh]
  have el : (cell.bounds.eLower : ℝ)≤s.e := by
    change ↑((1+cell.uLo+3*cell.qLo+2*beta cell.qLo*(1+cell.uLo)-2*eta cell.qHi*cell.qHi)-
      cell.correction*cell.bounds.aUpper)≤s.e0-s.κ*s.a
    push_cast
    apply sub_le_sub _ ka
    apply le_trans _ point.eLo
    gcongr
  have eu : s.e≤(cell.bounds.eUpper : ℝ) := by
    apply (sub_le_self _ (mul_nonneg klo az)).trans (point.eHi.trans _)
    dsimp only [Cell.bounds]; push_cast; gcongr ; first | positivity | norm_num
  have fl : (cell.bounds.fLower : ℝ)≤s.f := by
    change ↑((cell.uLo*cell.uLo/2+387/100*cell.uLo*cell.qLo+6*cell.qLo*cell.qLo-
      2*eta cell.qHi*cell.qHi*cell.qHi)-cell.correction*cell.bounds.bUpper)≤s.f0-s.κ*s.b
    push_cast
    apply sub_le_sub _ kb
    apply le_trans _ point.fLo
    gcongr ; first | positivity | norm_num
  have fu : s.f≤(cell.bounds.fUpper : ℝ) := by
    apply (sub_le_self _ (mul_nonneg klo bz)).trans (point.fHi.trans _)
    dsimp only [Cell.bounds]; push_cast; gcongr <;> first | positivity | norm_num
  have cases' : 0<s.f ∧ s.c/s.f≤(cell.bounds.ratioUpper : ℝ) := by
    cases entry : cell.jump with
    | false =>
      have kzero := le_antisymm (show s.κ≤0 by simpa [Cell.correction,entry] using khi) klo
      simp only [ScaledRow.f,kzero,zero_mul,sub_zero]
      refine ⟨fz,point.ratio.trans ?_⟩
      simp only [Cell.bounds,entry,Bool.false_eq_true,if_false]; push_cast
      gcongr
    | true =>
      have passes := all_pass cell valid
      have low : 0<(cell.bounds.fLower : ℝ) := by exact_mod_cast passes.2.2.2.2.2.2.2.1 entry
      have pos := low.trans_le fl
      refine ⟨pos,?_⟩
      apply (div_le_div₀ (cz.trans cu) cu low fl).trans_eq
      change C / (cell.bounds.fLower : ℝ) = ↑(cell.bounds.ratioUpper)
      simp only [C,Cell.bounds,Cell.cUpper,entry,if_true,Rat.cast_div]
  exact ⟨al,au,bl,bu,cz,dl,du,el,eu,cases'.1,fl,fu,cases'.2⟩

#print axioms endpoints_transport
end OrderedPartitions.CubicChamber.Box
