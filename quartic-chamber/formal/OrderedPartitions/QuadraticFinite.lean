import OrderedPartitions.QuadraticExactData.Cutoffs02To13
import OrderedPartitions.QuadraticExactData.Cutoffs14To25
import OrderedPartitions.QuadraticExactData.Cutoffs26To37
import OrderedPartitions.QuadraticExactData.Cutoffs38To49

/-! The exact finite sign certificate for every adjacent pair before the cubic range. -/

namespace OrderedPartitions.QuadraticExact

/-- Every cutoff in the finite remainder passes the executable integer test. -/
theorem checked_finite {j : ℕ} (lo : 2 ≤ j) (hi : j ≤ 49) : checkCutoff j = true := by
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

/-- The finite signed-remainder criterion on the original surjection-count polynomials. -/
theorem original_finite {j n : ℕ} (lo : 2 ≤ j) (hi : j ≤ 49)
    (hn : 2*j ≤ n) (hn' : n < 3*j) : OriginalSigns j n :=
  checkCutoff_sound (by omega) hn hn' (checked_finite lo hi)

#print axioms checked_finite
#print axioms original_finite

end OrderedPartitions.QuadraticExact
