import Mathlib

/-!
# A081391: Numbers k such that the central binomial coefficient C(2*k,k) has only one prime divisor whose exponent exceeds one.

Source: https://oeis.org/A081391
Credit: @darealpandaboi

Conjecture (Jon E. Schoenfield, Jul 29 2017): no terms after 786 (no more terms through 10^6).

Translation notes.
* k is a term when exactly one prime p satisfies p^2 | C(2k, k).
* This reading reproduces the listed data exactly: 3, 6, 7, 8, 9, 10, 11, 12, 16, 21, 22, 28,
  29, 30, 31, 36, 37, 54, 55, 57, 58, 110, 171, 784, 786 (checked by computer up to 2000).
* No terms after 786 is stated as: every term is at most 786.
-/

namespace OMA.S_oeis_a081391

/-- k is in A081391: exactly one prime has exponent at least 2 in C(2k, k). -/
def IsTerm (k : ℕ) : Prop :=
  {p : ℕ | p.Prime ∧ p ^ 2 ∣ Nat.choose (2 * k) k}.ncard = 1

theorem main : ∀ k : ℕ, IsTerm k → k ≤ 786 := by
  sorry

end OMA.S_oeis_a081391
