import OrderedPartitions.CubicLinearEnvelope
import OrderedPartitions.CubicSecondEnvelope
import OrderedPartitions.CubicQuarticCorrection

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

private theorem lin_price {j n s : ℕ} (hj : 64≤j) (jn : j≤n) (hn : 100≤n) (sn : s≤n) :
    |linearRaw j s/coeff n K-linearRaw j s|≤cEta j := by
  obtain ⟨lo,hi⟩ := raw_linear_bounds (by omega : 50≤j) s
  have le : (s:ℝ)≤n := by exact_mod_cast sn
  apply denominator_price hj jn hn (by linarith [Nat.cast_nonneg (α:=ℝ) s])
  nlinarith only [hi,le,Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ),show 0≤(n:ℝ)^3 by positivity]

private theorem quad_price {j n s : ℕ} (hj : 64≤j) (jn : j≤n) (hn : 100≤n) (sn : s≤n) :
    |quadraticRaw j s/coeff n K-quadraticRaw j s|≤cEta j := by
  obtain ⟨lo,hi⟩ := raw_quadratic_bounds (by omega : 50≤j) s
  have le : (s:ℝ)≤n := by exact_mod_cast sn
  have sq := pow_le_pow_left₀ (show 0≤(s:ℝ)+4 by positivity) (show (s:ℝ)+4≤n+4 by linarith) 2
  apply denominator_price hj jn hn ((by positivity : 0≤(s+1:ℝ)*(s+2)/2).trans lo)
  nlinarith only [hi,sq,Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ),show 0≤(n:ℝ)^3 by positivity]

theorem true_linear_envelopes {j m : ℕ} (hj : 64≤j) :
    let n := 3*j+m
    let t : ℝ := 2*j+m
    let a := normalizedMoment n j 1
    let d := normalizedMoment (n+1) j 1-a
    t+1.68+cBeta j*t-cEta j≤a ∧ a≤cMass j*(t+1.72)+cEta j ∧
    1+cBeta j-3*cEta j≤d ∧ d≤1+2*(cMass j-1)-cBeta j+3*cEta j := by
  dsimp only
  let u := 2*j+m
  have up : j≤u := by dsimp [u];omega
  have next : 3*j+m+1=u+1+j := by dsimp [u];omega
  have now : 3*j+m=u+j := by dsimp [u];omega
  rw [next,normalized_linear j (u+1) (by omega),now,normalized_linear j u (by omega)]
  have pc := abs_le.mp (lin_price (s:=u) (n:=u+j) hj (by omega) (by omega) (by omega))
  have pn := abs_le.mp (lin_price (s:=u+1) (n:=u+1+j) hj (by omega) (by omega) (by omega))
  have val := linear_raw_envelope hj up
  have inc := linear_step_envelope hj up
  have ur : (u:ℝ)=2*j+m := by dsimp [u];push_cast; rfl
  rw [ur] at val
  exact ⟨by linarith [pc.1,val.1],by linarith [pc.2,val.2],
    by linarith [inc.1,pn.1,pc.2],by linarith [inc.2,pn.2,pc.1]⟩

theorem true_quadratic_envelopes {j m : ℕ} (hj : 64≤j) :
    let n := 3*j+m
    let s : ℝ := j+m
    let b := normalizedMoment n j 2
    let e := normalizedMoment (n+1) j 2-b
    s^2/2+2.52*s+2+cBeta j*s^2-cEta j≤b ∧ b≤cMass j^2*(s^2/2+2.55*s+2.86)+cEta j ∧
    s+3+2*cBeta j*s-2*cEta j≤e ∧ e≤cMass j^2*(s+3.54)+2*cEta j := by
  dsimp only
  let u := j+m
  have up : j≤u := by dsimp [u];omega
  have next : 3*j+m+1=u+1+2*j := by dsimp [u];omega
  have now : 3*j+m=u+2*j := by dsimp [u];omega
  rw [next,normalized_quadratic j (u+1) (by omega),now,normalized_quadratic j u (by omega)]
  have pc := abs_le.mp (quad_price (s:=u) (n:=u+2*j) hj (by omega) (by omega) (by omega))
  have pn := abs_le.mp (quad_price (s:=u+1) (n:=u+1+2*j) hj (by omega) (by omega) (by omega))
  have val := quadratic_raw_envelope hj up
  have inc := quadratic_step_envelope hj up
  have ur : (u:ℝ)=(j:ℝ)+m := by dsimp [u];push_cast; rfl
  rw [ur] at val inc
  exact ⟨by linarith [pc.1,val.1],by linarith [pc.2,val.2],
    by linarith [inc.1,pn.1,pc.2],by linarith [inc.2,pn.2,pc.1]⟩

#print axioms true_linear_envelopes
#print axioms true_quadratic_envelopes
#print axioms true_cubic_envelopes
#print axioms relative_cubic
#print axioms true_quartic_correction
end OrderedPartitions.Kernel
