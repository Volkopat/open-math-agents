import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a003108

/-- OEIS A003108: number of partitions of `n` into positive cubes (`k ^ 3` for `k ≥ 1`). -/
noncomputable def a003108 (n : ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter (fun p : Nat.Partition n => ∀ x ∈ p.parts, ∃ k : ℕ, 1 ≤ k ∧ x = k ^ 3)).card

/-- Simon Plouffe's 1992 conjectured generating function for OEIS A003108:
`∑_{n ≥ 0} a(n) z^n = 1 / ((z + 1)(z^2 + 1)(z^4 + 1)(z - 1)^2)`,
equivalently `(1 - z - z^8 + z^9) * ∑_{n ≥ 0} a(n) z^n = 1`. -/
theorem main :
    ((1 : PowerSeries ℤ) - PowerSeries.X - PowerSeries.X ^ 8 + PowerSeries.X ^ 9) *
      PowerSeries.mk (fun n => (a003108 n : ℤ)) = 1 := by
  sorry

end OMA.S_oeis_a003108
