import OrderedPartitions.CubicFiniteReadout
import OrderedPartitions.CubicFiniteData.Cutoffs02To17
import OrderedPartitions.CubicFiniteData.Cutoffs18To29
import OrderedPartitions.CubicFiniteData.Cutoffs30To39
import OrderedPartitions.CubicFiniteData.Cutoffs40To47
import OrderedPartitions.CubicFiniteData.Cutoffs48To54
import OrderedPartitions.CubicFiniteData.Cutoffs55To59
import OrderedPartitions.CubicFiniteData.Cutoffs60To62
import OrderedPartitions.CubicFiniteData.Cutoffs63To63

/-! The entire finite complement for the cubic range on the original rows. -/

namespace OrderedPartitions.CubicFinite

/-- Every cutoff up to 63 passes the exact signed pseudo-remainder test. -/
theorem checked_finite {j : ℕ} (lo : 2 ≤ j) (hi : j ≤ 63) :
    checkCutoff j = true := by
  interval_cases j
  · exact cutoff02
  · exact cutoff03
  · exact cutoff04
  · exact cutoff05
  · exact cutoff06
  · exact cutoff07
  · exact cutoff08
  · exact cutoff09
  · exact cutoff10
  · exact cutoff11
  · exact cutoff12
  · exact cutoff13
  · exact cutoff14
  · exact cutoff15
  · exact cutoff16
  · exact cutoff17
  · exact cutoff18
  · exact cutoff19
  · exact cutoff20
  · exact cutoff21
  · exact cutoff22
  · exact cutoff23
  · exact cutoff24
  · exact cutoff25
  · exact cutoff26
  · exact cutoff27
  · exact cutoff28
  · exact cutoff29
  · exact cutoff30
  · exact cutoff31
  · exact cutoff32
  · exact cutoff33
  · exact cutoff34
  · exact cutoff35
  · exact cutoff36
  · exact cutoff37
  · exact cutoff38
  · exact cutoff39
  · exact cutoff40
  · exact cutoff41
  · exact cutoff42
  · exact cutoff43
  · exact cutoff44
  · exact cutoff45
  · exact cutoff46
  · exact cutoff47
  · exact cutoff48
  · exact cutoff49
  · exact cutoff50
  · exact cutoff51
  · exact cutoff52
  · exact cutoff53
  · exact cutoff54
  · exact cutoff55
  · exact cutoff56
  · exact cutoff57
  · exact cutoff58
  · exact cutoff59
  · exact cutoff60
  · exact cutoff61
  · exact cutoff62
  · exact cutoff63

/-- Exact root lists for the 2,015 original pairs, including 62 quartic entries. -/
theorem original_finite {j n : ℕ} (hj : 2 ≤ j) (hj' : j ≤ 63)
    (lo : 3*j ≤ n) (hi : n < 4*j) :
    QuadraticOrder.CubicAdjacent (row n j) (row (n+1) j) (n+1 = 4*j) :=
  original_of_check (by omega) lo hi (checked_finite hj hj')

#print axioms checked_finite
#print axioms original_finite

end OrderedPartitions.CubicFinite
