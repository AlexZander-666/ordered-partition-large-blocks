import OrderedPartitions.RenewalNumeric

/-! The uniform ordered Bell coefficient bound on the original ordered-partition rows. -/

namespace OrderedPartitions.Renewal

/-- For every cutoff the free, normalized row agrees with the simple-pole
approximation at an explicitly controlled geometric error, starting at rank zero. -/
theorem ordered_bell_geometric_error {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    |2 * (Real.log 2)^(n+1) * (row n j).eval 1 / n.factorial - 1| ≤ 1/(2*8^n) := by
  apply original_error_from_rational (L := rhoLower) (U := rhoUpper)
    (by decide +kernel) log_two_interval.1 log_two_interval.2 (by decide +kernel)
    RenewalData.bell RenewalData.bell_real checked_initial checked_residual checked_forcing hj n

#print axioms ordered_bell_geometric_error
end OrderedPartitions.Renewal
