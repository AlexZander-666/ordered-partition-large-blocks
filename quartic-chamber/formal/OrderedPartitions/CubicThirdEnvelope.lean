import OrderedPartitions.CubicMarkerMass
import OrderedPartitions.FirstCubicPairMoment

noncomputable section
open PowerSeries Finset
namespace OrderedPartitions.Kernel

theorem conv_majorant {j h : ℕ} (hj : 64≤j) (s : ℕ) (F : ℕ→ℝ) {U : ℝ}
    (non : ∀i≤s,0≤F i) (cap : ∀i≤s,F i≤U) (un : 0≤U) :
    F s≤convSeq (cWeight j h) F s ∧ convSeq (cWeight j h) F s≤cMass j^h*U := by
  have hh := conv_band _ F s (cWeight_zero j h) (cWeight_nonneg j h)
    (cWeight_mass hj h _) un (fun i hi ↦ ⟨non i hi,cap i hi⟩)
  exact ⟨hh.1,by linarith [hh.2,cap s le_rfl]⟩

private theorem vUpper_mono {x y : ℝ} (hx : 0≤x) (xy : x≤y) : vUpper x ≤ vUpper y := by
  unfold vUpper; gcongr

private theorem dvUpper_mono {x y : ℝ} (hx : 0≤x) (xy : x≤y) : dvUpper x ≤ dvUpper y := by
  unfold dvUpper; gcongr

theorem cubic_raw_range {j : ℕ} (hj : 64≤j) (s : ℕ) :
    (s:ℝ)^3/6≤cubicRaw j s ∧ cubicRaw j s≤cMass j^3 * vUpper s := by
  rw [cRaw_conv]
  have b := conv_majorant (h:=3) (U:=vUpper s) hj s v (fun i _ ↦ (by positivity : (0:ℝ)≤(i:ℝ)^3/6).trans (v_range i).1)
    (fun i hi ↦ (v_range i).2.trans (vUpper_mono (by positivity) (by exact_mod_cast hi)))
    (by unfold vUpper; positivity)
  exact ⟨(v_range s).1.trans b.1,b.2⟩

theorem cubic_raw_increment {j : ℕ} (hj : 64≤j) (s : ℕ) :
    dvLower s≤cubicRaw j (s+1)-cubicRaw j s ∧
      cubicRaw j (s+1)-cubicRaw j s≤cMass j^3*dvUpper s := by
  rw [cRaw_conv,cRaw_conv,conv_delta]
  have zK : constantCoeff K=2*rho := by
    rw [← coeff_zero_eq_constantCoeff_apply,k_row (j:=1) (by decide),row_zero (by decide)]
    simp
  have zd : deltaSeq v 0 = (2*rho)^4 := by simp [deltaSeq,v,coeff_zero_eq_constantCoeff_apply,zK]
  have nn (i : ℕ) : 0≤deltaSeq v i := by
    cases i with
    | zero => rw [zd]; positivity
    | succ i => exact (by unfold dvLower; positivity : (0:ℝ)≤dvLower i).trans (dv_range i).1
  have hi (i : ℕ) (h : i≤s+1) : deltaSeq v i≤dvUpper s := by
    cases i with
    | zero =>
      have h4 := pow_le_pow_left₀ (show 0≤2*rho by linarith [rho_interval.1])
        (show 2*rho≤1.4 by linarith [rho_interval.2]) 4
      rw [zd]; unfold dvUpper
      nlinarith only [h4,sq_nonneg (s:ℝ),Nat.cast_nonneg (α:=ℝ) s]
    | succ i => exact (dv_range i).2.trans (dvUpper_mono (by positivity) (by exact_mod_cast (by omega : i≤s)))
  have b := conv_majorant (h:=3) hj (s+1) (deltaSeq v) (fun i _ ↦ nn i) hi (by unfold dvUpper; positivity)
  exact ⟨(dv_range s).1.trans b.1,b.2⟩

private theorem cubic_decay {n : ℕ} (hn : 100≤n) :
    200*(n:ℝ)*((n:ℝ)+7)^3 ≤ (8:ℝ)^n := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n h ih =>
    rw [pow_succ (8:ℝ) n]; push_cast
    have nR : (100:ℝ)≤n := by exact_mod_cast h
    have a : (n:ℝ)+1 ≤ 1.01*n := by linarith
    have c : (n:ℝ)+1+7 ≤ 1.01*(n+7) := by linarith
    have p := mul_le_mul a (pow_le_pow_left₀ (by positivity) c 3) (by positivity) (by positivity)
    nlinarith only [p,ih,Nat.cast_nonneg (α:=ℝ) n,pow_nonneg (show (0:ℝ)≤8 by norm_num) n,
      show 0≤(n:ℝ)*((n:ℝ)+7)^3 by positivity]

theorem denominator_price {j n : ℕ} (hj : 64≤j) (jn : j≤n) (hn : 100≤n) {A : ℝ}
    (non : 0≤A) (cap : A≤2*((n:ℝ)+7)^3) : |A/coeff n K-A| ≤ cEta j := by
  have jp : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have nR : (j:ℝ)≤n := by exact_mod_cast jn
  have pos := k_pos n
  have e : |coeff n K-1|≤1/(2*8^n) := eps_bound n
  have half : 1/2 ≤ coeff n K := by
    have e' : 1/(2*(8:ℝ)^n)≤1/2 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤8) (n:=n)])
    linarith [(abs_le.mp e).1]
  rw [show A/coeff n K-A= -(A*(coeff n K-1))/coeff n K by field_simp; ring,
    abs_div,abs_neg,abs_mul,abs_of_pos pos,abs_of_nonneg non]
  apply (div_le_iff₀ pos).mpr
  have prod := mul_le_mul cap e (abs_nonneg _) (by positivity)
  have pc := cubic_decay hn
  have nj := mul_le_mul_of_nonneg_right nR (show 0≤((n:ℝ)+7)^3 by positivity)
  have price : 2*((n:ℝ)+7)^3*(1/(2*8^n)) ≤ cEta j/2 := by
    dsimp [cEta,cq]
    field_simp
    nlinarith only [pc,nj]
  have eta : 0≤cEta j := by dsimp [cEta]; positivity [cq_pos hj]
  linarith only [prod.trans price,mul_le_mul_of_nonneg_left half eta]

theorem normalized_cubic (j s : ℕ) (hj : 1≤j) :
    normalizedMoment (s+3*j) j 3 = cubicRaw j s/coeff (s+3*j) K :=
  normalizedMoment_coeff hj 3 s

private theorem cubic_price {j n s : ℕ} (hj : 64≤j) (jn : j≤n) (hn : 100≤n) (sn : s≤n) :
    |cubicRaw j s/coeff n K-cubicRaw j s| ≤ cEta j := by
  obtain ⟨lo,hi⟩ := cubic_raw_range hj s
  have snR : (s:ℝ)≤n := by exact_mod_cast sn
  apply denominator_price hj jn hn ((by positivity : (0:ℝ)≤(s:ℝ)^3/6).trans lo)
  have vcap : vUpper s≤((n:ℝ)+7)^3 := by
    apply (vUpper_mono (by positivity) snR).trans
    unfold vUpper
    nlinarith only [Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ),show (0:ℝ)≤(n:ℝ)^3 by positivity]
  have mcap := pow_le_pow_left₀ (mass_pos hj).le (mass_limits hj).2 3
  apply hi.trans
  exact (mul_le_mul mcap vcap (by unfold vUpper;positivity) (by norm_num)).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))

theorem true_cubic_envelopes {j m : ℕ} (hj : 64≤j) :
    let n := 3*j+m
    let c := normalizedMoment n j 3
    let f := normalizedMoment (n+1) j 3-c
    (m:ℝ)^3/6-cEta j≤c ∧ c≤cMass j^3*vUpper m+cEta j ∧
    dvLower m-2*cEta j≤f ∧ f≤cMass j^3*dvUpper m+2*cEta j := by
  dsimp only
  have e : 3*j+m=m+3*j := by omega
  have e' : 3*j+m+1=m+1+3*j := by omega
  have j1 : 1≤j := by omega
  rw [e', normalized_cubic j (m+1) j1, e, normalized_cubic j m j1]
  have p := abs_le.mp (cubic_price (s:=m) (n:=m+3*j) hj (by omega) (by omega) (by omega))
  have pp := abs_le.mp (cubic_price (s:=m+1) (n:=m+1+3*j) hj (by omega) (by omega) (by omega))
  have b := cubic_raw_range hj m
  have d := cubic_raw_increment hj m
  refine ⟨?_,?_,?_,?_⟩
  · linarith [b.1,p.1]
  · linarith [b.2,p.2]
  · linarith [d.1,p.2,pp.1]
  · linarith [d.2,p.1,pp.2]

#print axioms true_cubic_envelopes
#print axioms denominator_price
end OrderedPartitions.Kernel
