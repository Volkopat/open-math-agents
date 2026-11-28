import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a002843

/-- A partition of `n` into parts `1/2, 3/4, 7/8, 15/16, ...`, represented as a multiset of
positive integers `k ≥ 1` where each `k` denotes the part `(2^k - 1) / 2^k`. -/
def IsDyadicPartition (n : ℕ) (s : Multiset ℕ) : Prop :=
  (∀ k ∈ s, 1 ≤ k) ∧ (s.map (fun k : ℕ => ((2 ^ k - 1 : ℚ) / (2 ^ k : ℚ)))).sum = (n : ℚ)

/-- OEIS A002843(n): Number of partitions of `n` into parts `1/2, 3/4, 7/8, 15/16, ...`. -/
noncomputable def A002843 (n : ℕ) : ℕ :=
  Set.ncard { s : Multiset ℕ | IsDyadicPartition n s }

/-- Conjecture (Simon Plouffe, 1992; OEIS A002843): The ordinary generating function of
`A002843(n)` equals `(z^2 + z + 1) * (z - 1)^2 / (1 - 2*z - z^3 + 3*z^4)`, i.e.
`(1 - 2*X - X^3 + 3*X^4) * (∑_{n ≥ 0} A002843(n) * X^n) = (X^2 + X + 1) * (X - 1)^2`
in `ℤ⟦X⟧`. -/
theorem main :
    (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X - PowerSeries.X ^ 3 +
        PowerSeries.C (3 : ℤ) * PowerSeries.X ^ 4) *
      PowerSeries.mk (fun n => (A002843 n : ℤ)) =
      (PowerSeries.X ^ 2 + PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2 := by
  sorry

end OMA.S_oeis_a002843
