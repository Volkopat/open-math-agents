import OMAStatements.S_oeis_a109799
import Mathlib

/-! A109799 restated as a question about Mersenne primes that are also Wagstaff exponents.

For an odd prime `p`, `2^p - 1 + 2 = 2^p + 1` is divisible by `3`, so it is never prime, and it
is a semiprime exactly when the Wagstaff number `(2^p + 1) / 3` is prime (`Ω(3 m) = 1 + Ω(m)`).
So `2^p - 1` is a Chen prime exactly when `2^p - 1` is a Mersenne prime and `(2^p + 1) / 3` is
a Wagstaff prime. That is `H1`, a structural equivalence for every odd prime `p`, not progress
on the conjecture.

`H2` is the open rest: no odd prime `p > 127` makes both `2^p - 1` and `(2^p + 1) / 3` prime
(the case of the New Mersenne Conjecture with both numbers prime). `p = 2` gives `3`, a Chen
prime, and `2 ≤ 127`.
-/

namespace OMA.R_oeis_a109799_R1

open OMA.S_oeis_a109799

/-- For odd primes `p`: `2^p - 1` is a Chen prime iff it is prime and `(2^p + 1) / 3` is prime. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 3 ≤ p →
  (IsChenPrime (2 ^ p - 1) ↔ (2 ^ p - 1).Prime ∧ ((2 ^ p + 1) / 3).Prime)

/-- The open rest: Mersenne and Wagstaff primes with the same odd prime exponent stop at 127. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 3 ≤ p → (2 ^ p - 1).Prime → ((2 ^ p + 1) / 3).Prime →
  p ≤ 127

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a109799.main := by
  intro h1 h2 p hp hc
  by_cases h3 : 3 ≤ p
  · obtain ⟨a, b⟩ := (h1 p hp h3).1 hc
    exact h2 p hp h3 a b
  · omega

end OMA.R_oeis_a109799_R1
