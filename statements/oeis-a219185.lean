import Mathlib

/-!
# A219185: Number of prime pairs {p,q} (p>q) with 3(p-q)-1 and 3(p-q)+1 both prime such that p+(1+(n mod 2))q=n.

Source: https://oeis.org/A219185
Credit: @eltociear

`a(n)` (offset 1) counts the pairs of primes `p > q` with `3(p - q) - 1` and `3(p - q) + 1` both
prime and `p + (1 + (n mod 2)) q = n`; so `n = p + q` for even `n` and `n = p + 2q` for odd `n`
(`a(11) = 1` from `11 = 5 + 2·3`; `a(16) = 2` from `16 = 11 + 5 = 13 + 3`). The entry conjectures
(Zhi-Wei Sun):

  a(n) > 0 for all odd n > 4676 and even n > 30986.

`main` states that such a pair exists for every odd `n > 4676` and every even `n > 30986`.
Since `p > q`, `p - q ≥ 1` and both natural-number subtractions are exact.
-/

namespace OMA.S_oeis_a219185

/-- The pair `(p, q)` is counted by A219185 at `n`. -/
def Counted (n p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ q < p ∧ (3 * (p - q) - 1).Prime ∧ (3 * (p - q) + 1).Prime ∧
    p + (1 + n % 2) * q = n

/-- The conjecture in OEIS A219185: `a(n) > 0` for odd `n > 4676` and even `n > 30986`. -/
theorem main : ∀ n : ℕ, ((Odd n ∧ 4676 < n) ∨ (Even n ∧ 30986 < n)) →
    ∃ p q : ℕ, Counted n p q := by
  sorry

end OMA.S_oeis_a219185
