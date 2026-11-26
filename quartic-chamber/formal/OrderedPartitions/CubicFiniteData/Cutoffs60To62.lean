import OrderedPartitions.CubicFiniteSigns

/-! Kernel decisions for each cutoff in this block of the cubic range. -/

namespace OrderedPartitions.CubicFinite

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff60 : checkCutoff 60 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff61 : checkCutoff 61 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff62 : checkCutoff 62 = true := by decide +kernel

end OrderedPartitions.CubicFinite
