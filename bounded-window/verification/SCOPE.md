# Statement and byte correspondence

The 76-module published bounded-ratio project proves the statement for h=1.
The 82-module companion proves the interlacing of complete original root
arrays simultaneously for each integer h from 1 through j under the same
fixed cap n≤Cj and one bound J(C). The second strict inequality comes
from a new h=j comparison. The integer branch needs the relative leading
coefficient inequality and a comparison of both roots escaping to minus
infinity. Taking only repeated adjacent comparisons does not supply that
cross-rank gap inequality.

The two source archives share 75 byte-identical Lean modules and identical
Lean, Lake and dependency locks. The earlier archive contains its own
exceptional-rows corollary. The new archive adds seven modules, rooted
at OrderedPartitions.HardRodWindowVerified, and preserves the earlier
bounded-ratio theorem through its import closure. These results impose a
fixed ratio cap and state existence of its threshold. The proof includes
low-degree entrance D=1 and exact m=0.

- Paper Theorem 1 — OrderedPartitions.original_full_window_bounded_ratio
- Full period — OrderedPartitions.original_full_period_bounded_ratio
- Paper Lemma 2 — OrderedPartitions.Kernel.full_period_leading_bound
- Right-rank composition — OrderedPartitions.RootTracking.orderedPair_window_of_period

Frozen source SHA-256 bf246e653541b772a63928ec519de30b3094221deab80727d7ee95a9488144ea.
The sealed Spark verification records 82 warning-as-error builds, 82
separate Lean kernel replays, 212 source and eight targeted axiom reports.
[Earlier adjacent-row preprint](https://doi.org/10.5281/zenodo.24570914)
