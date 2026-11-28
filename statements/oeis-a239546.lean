import Mathlib

/-!
# A239546: Sum of the prime factors of n, where n runs through perfect numbers

Source: https://oeis.org/A239546

Conjecture (OEIS A239546):
For every perfect number `m`, the sum of its distinct prime factors equals `p + 2`
for some Mersenne prime `p = 2 ^ k - 1` (i.e., `a(n) = A000668(n) + 2`).

Conventions:
- Offset: `1`; first terms: `5, 9, 33, 129, 8193, 131073, ...`
  (for `m = 6`, prime factors `{2, 3}`, sum `5 = 3 + 2`;
   for `m = 28`, prime factors `{2, 7}`, sum `9 = 7 + 2`).
- Expressing the statement directly over all perfect numbers avoids assuming
  the infinitude of perfect numbers.
-/

namespace OMA.S_oeis_a239546

/-- Predicate stating that `m` is a perfect number (OEIS A000396). -/
def IsPerfect (m : ℕ) : Prop :=
  0 < m ∧ (Nat.divisors m).sum id = 2 * m

/-- Predicate stating that `p` is a Mersenne prime (OEIS A000668). -/
def IsMersennePrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ k : ℕ, p = 2 ^ k - 1

/-- Conjecture: for every perfect number `m`, the sum of its distinct prime factors
is `2` more than a Mersenne prime. -/
theorem main :
    ∀ m : ℕ, IsPerfect m →
      ∃ p : ℕ, IsMersennePrime p ∧ m.primeFactors.sum id = p + 2 := by
  sorry

end OMA.S_oeis_a239546
