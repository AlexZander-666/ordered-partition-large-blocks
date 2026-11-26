import OrderedPartitions.CubicThirdEnvelope

noncomputable section
open PowerSeries
namespace OrderedPartitions.Kernel

theorem eta_range {j : ℕ} (hj : 64≤j) : 0≤cEta j ∧ cEta j≤1/6400 := by
  unfold cEta
  constructor <;> linarith [cq_pos hj,cq_bound hj]

theorem relative_cubic {j m : ℕ} (hj : 64≤j) :
    let n := 3*j+m
    let c := normalizedMoment n j 3
    let f := normalizedMoment (n+1) j 3-c
    0<f ∧ c/f≤cMass j^3*((m:ℝ)+3)/3 := by
  dsimp only
  obtain ⟨_,hi,lo,_⟩ := true_cubic_envelopes (m:=m) hj
  obtain ⟨eta,cap⟩ := eta_range hj
  have fm : 0<dvLower m-2*cEta j := by
    unfold dvLower
    nlinarith only [cap,Nat.cast_nonneg (α:=ℝ) m,sq_nonneg (m:ℝ)]
  have pos := fm.trans_le lo
  refine ⟨pos,(div_le_iff₀ pos).mpr ?_⟩
  have M : (1:ℝ)≤cMass j^3 := one_le_pow₀ (mass_limits hj).1
  have h : 3*(vUpper m+cEta j) ≤ ((m:ℝ)+3)*(dvLower m-2*cEta j) := by
    unfold vUpper dvLower
    nlinarith only [cap,mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg (α:=ℝ) m),
      Nat.cast_nonneg (α:=ℝ) m,sq_nonneg (m:ℝ)]
  have l := mul_le_mul_of_nonneg_left lo (show 0≤(m:ℝ)+3 by positivity)
  have r := mul_le_mul_of_nonneg_left (h.trans l) (show 0≤cMass j^3 by linarith)
  nlinarith only [hi,r,mul_le_mul_of_nonneg_right M eta]

theorem true_quartic_correction {j m : ℕ} (hj : 64≤j) (hm : m<j) :
    let n := 3*j+m
    let c := normalizedMoment n j 3
    let z := normalizedMoment (n+1) j 4
    0≤z/c ∧ z/c≤50/(j:ℝ)^3 ∧ (m+1<j → z=0) ∧ (m+1=j → 0<z) := by
  dsimp only
  have j1 : 1≤j := by omega
  have J : (64:ℝ)≤j := by exact_mod_cast hj
  by_cases e : m+1=j
  · have eqn : 3*j+m+1=4*j := by omega
    rw [eqn,(moment_entry_and_successor j1 4).1]
    have rho0 : 0<2*rho := by linarith [rho_interval.1]
    have k0 := k_pos (4*j)
    have z0 : 0<(2*rho)^(4+1)/coeff (4*j) K := by positivity
    have p : (8:ℝ)^3≤8^(4*j) := pow_le_pow_right₀ (by norm_num) (by omega)
    have ke := (abs_le.mp (eps_bound (4*j))).1
    have small : (1:ℝ)/(2*8^(4*j))≤1/1000 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    unfold eps at ke
    have zcap : (2*rho)^(4+1)/coeff (4*j) K ≤6 := (div_le_iff₀ k0).mpr (by
      have bound := pow_le_pow_left₀ rho0.le (show 2*rho≤1.4 by linarith [rho_interval.2]) 5
      change (2*rho)^5 ≤ _
      linarith only [ke,small,bound])
    have em : (m:ℝ)+1=j := by exact_mod_cast e
    have mc := pow_le_pow_left₀ (show 0≤(63/64:ℝ)*(j:ℝ) by positivity)
      (show (63/64:ℝ)*(j:ℝ)≤m by linarith) 3
    have j3 : (64:ℝ)^3 ≤ (j:ℝ)^3 := pow_le_pow_left₀ (by norm_num) J 3
    have firm := (true_cubic_envelopes (m:=m) hj).1
    have c0 : 6*(j:ℝ)^3/50 < normalizedMoment (3*j+m) j 3 := by
      nlinarith only [mc,j3,firm,(eta_range hj).2]
    have cp : 0<normalizedMoment (3*j+m) j 3 := lt_trans (by positivity) c0
    refine ⟨(div_pos z0 cp).le,?_,by omega,fun _ ↦ z0⟩
    rw [div_le_div_iff₀ cp (by positivity : (0:ℝ)<(j:ℝ)^3)]
    nlinarith only [c0,mul_le_mul_of_nonneg_right zcap (show 0≤(j:ℝ)^3 by positivity)]
  · rw [normalized_before j1 (by omega : 3*j+m+1<4*j),zero_div]
    exact ⟨le_rfl,by positivity,fun _ ↦ rfl,fun h ↦ (e h).elim⟩

#print axioms relative_cubic
#print axioms true_quartic_correction
end OrderedPartitions.Kernel
