import Mathlib

/-!
# A213210: Numbers n such that n and n + 8 are prime and there is a power of two in the interval (n,n+8).

Source: https://oeis.org/A213210
Credit: @luciusacarr

Data: 3, 5, 11, 29, 59, 4091, 262139.

The entry says: it is a conjecture that this sequence is finite. A search around 2^n was done
up to 2^1500. `main` states that conjecture.

Reading of the source:
* `(n, n+8)` is the open interval: some power of two `2^k` satisfies `n < 2^k < n + 8`.
* `n` and `n + 8` are both required to be prime; nothing is said about the numbers between them.
* With this reading the terms below 10^6 are exactly the seven listed (checked numerically).
-/

namespace OMA.S_oeis_a213210

/-- The terms of A213210. -/
def S : Set ℕ := {n | n.Prime ∧ (n + 8).Prime ∧ ∃ k : ℕ, n < 2 ^ k ∧ 2 ^ k < n + 8}

theorem main :
    -- The sequence is finite.
    S.Finite := by
  sorry

end OMA.S_oeis_a213210
