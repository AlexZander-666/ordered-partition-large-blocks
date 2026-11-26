import OrderedPartitions.CubicFiniteSigns

/-! Kernel decisions for each cutoff in this block of the cubic range. -/

namespace OrderedPartitions.CubicFinite

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff48 : checkCutoff 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff49 : checkCutoff 49 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff50 : checkCutoff 50 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff51 : checkCutoff 51 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff52 : checkCutoff 52 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff53 : checkCutoff 53 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cutoff54 : checkCutoff 54 = true := by decide +kernel

end OrderedPartitions.CubicFinite
