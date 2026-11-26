import OrderedPartitions.CubicChamberBoxes

/-! Every ordinary and possible quartic cell of the rational grid passes the tests. -/

namespace OrderedPartitions.CubicChamber.Box

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkBand0 : ∀ iu : Fin 128, ∀ jump : Bool,
    (Cell.mk 0 iu jump).Valid → (Cell.mk 0 iu jump).Passes := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkBand1 : ∀ iu : Fin 128, ∀ jump : Bool,
    (Cell.mk 1 iu jump).Valid → (Cell.mk 1 iu jump).Passes := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkBand2 : ∀ iu : Fin 128, ∀ jump : Bool,
    (Cell.mk 2 iu jump).Valid → (Cell.mk 2 iu jump).Passes := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkBand3 : ∀ iu : Fin 128, ∀ jump : Bool,
    (Cell.mk 3 iu jump).Valid → (Cell.mk 3 iu jump).Passes := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkBand4 : ∀ iu : Fin 128, ∀ jump : Bool,
    (Cell.mk 4 iu jump).Valid → (Cell.mk 4 iu jump).Passes := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkBand5 : ∀ iu : Fin 128, ∀ jump : Bool,
    (Cell.mk 5 iu jump).Valid → (Cell.mk 5 iu jump).Passes := by decide +kernel

theorem all_pass (cell : Cell) (valid : cell.Valid) : cell.Passes := by
  rcases cell with ⟨iq, iu, jump⟩
  fin_cases iq
  · exact checkBand0 iu jump valid
  · exact checkBand1 iu jump valid
  · exact checkBand2 iu jump valid
  · exact checkBand3 iu jump valid
  · exact checkBand4 iu jump valid
  · exact checkBand5 iu jump valid

/-- The ordinary grid has 768 cells and the quartic line meets 9 cells. -/
theorem cell_counts : (allCells false).length = 768 ∧ (allCells true).length = 9 := by
  decide +kernel

#print axioms all_pass
#print axioms cell_counts

end OrderedPartitions.CubicChamber.Box
