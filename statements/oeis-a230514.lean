import Mathlib

/-!
# A230514: n = a + b + c with a(a+1)-1, b(b+1)-1, c(c+1)-1 Sophie Germain primes

Source: https://oeis.org/A230514

A230514 (offset 1): `a(n)` is the number of ways to write `n = a + b + c` (`0 < a ≤ b ≤ c`) such
that all the three numbers `a*(a+1) - 1`, `b*(b+1) - 1`, `c*(c+1) - 1` are Sophie Germain primes.
For example `a(10) = 2` since `10 = 2 + 2 + 6 = 2 + 3 + 5`, and `2*3 - 1 = 5`, `6*7 - 1 = 41`,
`3*4 - 1 = 11`, `5*6 - 1 = 29` are all Sophie Germain primes.

Conjecture (Zhi-Wei Sun, Oct 21 2013): `a(n) > 0` for all `n > 5`. The entry notes that this has
been verified for `n` up to `10^9` (Mauro Fiorentini, Sep 22 2023).

Since `a(n)` counts the triples `0 < a ≤ b ≤ c` with `a + b + c = n` and the three numbers
Sophie Germain primes, `a(n) > 0` says exactly that such a triple exists, and the conjecture is
stated in that form.

Conventions:
- A Sophie Germain prime is a prime `p` such that `2p + 1` is also prime.
- Everything is in `ℕ`; `x*(x+1) - 1` is an exact subtraction for `x > 0`.
-/

namespace OMA.S_oeis_a230514

/-- A Sophie Germain prime: a prime `p` with `2p + 1` also prime. -/
def IsSophieGermain (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)

theorem main :
    ∀ n : ℕ, 5 < n →
      ∃ a b c : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ c ∧ a + b + c = n ∧
        IsSophieGermain (a * (a + 1) - 1) ∧ IsSophieGermain (b * (b + 1) - 1) ∧
        IsSophieGermain (c * (c + 1) - 1) := by
  sorry

end OMA.S_oeis_a230514
