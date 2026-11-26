import OrderedPartitions.CubicFiniteSigns

/-! Kernel decisions for each cutoff in this block of the cubic range. -/

namespace OrderedPartitions.CubicFinite

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff55 : checkCutoff 55 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff56 : checkCutoff 56 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff57 : checkCutoff 57 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff58 : checkCutoff 58 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff59 : checkCutoff 59 = true := by decide +kernel

end OrderedPartitions.CubicFinite
