import OrderedPartitions.CubicFiniteSigns

/-! Kernel decisions for each cutoff in this block of the cubic range. -/

namespace OrderedPartitions.CubicFinite

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff63 : checkCutoff 63 = true := by decide +kernel

end OrderedPartitions.CubicFinite
