import Mathlib

/-!
# A222219: Numbers n such that n and n + 18 are prime and there is a power of two in the interval (n,n+18).

Source: https://oeis.org/A222219
Credit: @luciusacarr

Data: 5, 11, 13, 19, 23, 29, 53, 61, 113, 239, 251, 503, 1013, 1021, 4093, 8191, 65519, 65521,
262133, 1048571, 4194301, 302231454903657293676533.

The entry says: it is a conjecture that this sequence is finite. A search around 2^n was done
up to 2^1500. `main` states that conjecture.

Reading of the source:
* `(n, n+18)` is the open interval: some power of two `2^k` satisfies `n < 2^k < n + 18`.
* `n` and `n + 18` are both required to be prime; nothing is said about the numbers between them.
* With this reading the terms below 2^89 are exactly the twenty-two listed (checked numerically).
-/

namespace OMA.S_oeis_a222219

/-- The terms of A222219. -/
def S : Set ℕ := {n | n.Prime ∧ (n + 18).Prime ∧ ∃ k : ℕ, n < 2 ^ k ∧ 2 ^ k < n + 18}

theorem main :
    -- The sequence is finite.
    S.Finite := by
  sorry

end OMA.S_oeis_a222219
