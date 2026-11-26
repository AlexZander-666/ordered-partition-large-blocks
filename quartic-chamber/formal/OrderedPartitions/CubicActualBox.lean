import OrderedPartitions.CubicEndpointTransfer

noncomputable section
namespace OrderedPartitions.CubicChamber.Box
open OrderedPartitions.Kernel

theorem actual_encloses {j m : ℕ} (hj : 64≤j) (hm : m<j) (cell : Cell)
    (flag : cell.jump=decide (m+1=j)) (valid : cell.Valid)
    (inc : cell.Contains (1/(j:ℝ)) ((m:ℝ)/j)) :
    let row := actualRow j m
    Encloses cell row.a row.b row.c row.d row.e row.f := by
  have jp : 0<(j:ℝ) := by exact_mod_cast (show 0<j by omega)
  have ql0 : 0≤(cell.qLo : ℝ) := by unfold Cell.qLo; positivity
  have qlim : (cell.qHi : ℝ)≤1/64 := by
    have le : ((cell.iq.val:ℕ):ℝ)+1≤6 := by exact_mod_cast cell.iq.isLt
    unfold Cell.qHi; push_cast; linarith
  have M : cMass j ≤ (mass cell.qHi : ℝ) := by
    unfold cMass mass cq;push_cast
    rw [← one_div]
    apply one_div_le_one_div_of_le (by linarith)
    linarith only [inc.2.1]
  have b : (beta cell.qLo : ℝ)≤cBeta j := by
    unfold beta cBeta cq; push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [inc.1]
  have e : cEta j≤(eta cell.qHi : ℝ) := by
    unfold cEta eta cq; push_cast;linarith only [inc.2.1]
  have pos (h : ℕ) (small : h≤2) : 0<normalizedMoment (3*j+m) j (h+1) := by
    apply (normalizedMoment_pos_iff (by omega) h).2
    nlinarith only [Nat.mul_le_mul_right j small,Nat.zero_le m]
  have az : 0≤(actualRow j m).a := (div_pos (pos 0 (by decide)) jp).le
  have bz : 0≤(actualRow j m).b := (div_pos (pos 1 (by decide)) (pow_pos jp 2)).le
  have cz : 0≤(actualRow j m).c := (div_pos (pos 2 (by decide)) (pow_pos jp 3)).le
  have fz : 0<(actualRow j m).f0 := div_pos (relative_cubic (m:=m) hj).1 (pow_pos jp 2)
  obtain ⟨kn,kb,ordinary,_⟩ := true_quartic_correction hj hm
  have kcap : (actualRow j m).κ≤(cell.correction : ℝ) := by
    cases entry : cell.jump with
    | false =>
      have net : m+1≠j := by simpa [entry] using flag.symm
      simp only [actualRow,ordinary (by omega),zero_div,Cell.correction,entry,Bool.false_eq_true,if_false,Rat.cast_zero]
      exact le_rfl
    | true =>
      apply kb.trans
      simp only [Cell.correction,entry,if_true,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
      rw [show 50/(j:ℝ)^3=50*(1/(j:ℝ))^3 by ring]
      gcongr
      exact inc.2.1
  apply endpoints_transport cell (actualRow j m) (actual_point_bounds hj) inc (by positivity) (by positivity)
    (mass_pos hj).le _ (eta_range hj).1 M b e az bz cz fz kn kcap valid
  unfold cBeta cq; positivity

/-- The admitted rational cell carrying the true lower and upper row. -/
theorem actual_box_exists {j m : ℕ} (hj : 64≤j) (hm : m<j) :
    let row := actualRow j m
    ∃ cell : Cell, cell.Valid ∧ cell.jump=decide (m+1=j) ∧
      Encloses cell row.a row.b row.c row.d row.e row.f := by
  obtain ⟨cell,flag,valid,inc⟩ := cover_dimensions hj hm
  exact ⟨cell,valid,flag,actual_encloses hj hm cell flag valid inc⟩

#print axioms actual_encloses
#print axioms actual_box_exists
end OrderedPartitions.CubicChamber.Box
