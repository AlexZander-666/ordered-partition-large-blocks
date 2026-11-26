import OrderedPartitions.RenewalData
import OrderedPartitions.RenewalLogInterval
import OrderedPartitions.RenewalRationalBridge

/-! Finite rational checks used by the ordered Bell residual certificate. -/
namespace OrderedPartitions.Renewal
open OrderedPartitions.RenewalData

set_option maxHeartbeats 30000000
set_option maxRecDepth 16000

private theorem initial_table : ∀ i : Fin 49,
    finiteCheckError rhoLower rhoUpper bell i ≤ 1/2 := by decide +kernel

theorem checked_initial (i : ℕ) (hi : i ≤ 48) :
    finiteCheckError rhoLower rhoUpper bell i ≤ 1/2 :=
  initial_table ⟨i,by omega⟩

theorem checked_residual :
    finiteCost rhoLower rhoUpper bell 2 1 ≤ 697279/1000000 := by decide +kernel

theorem checked_forcing :
    finiteCost rhoLower rhoUpper bell 4 2 ≤ 131844/1000000 := by decide +kernel

#print axioms checked_initial
#print axioms checked_residual
#print axioms checked_forcing
end OrderedPartitions.Renewal
