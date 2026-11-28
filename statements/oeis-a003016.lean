import Mathlib

/-!
# OEIS A003016: Singmaster's conjecture on multiplicities in Pascal's triangle

Source: https://oeis.org/A003016
Credit: @sntntHb

A003016: number of occurrences of `n` as an entry in rows `<= n` of Pascal's triangle
(offset 0: 0, 3, 1, 2, 2, 2, 3, 2, 2, 2, 4, ...).

Conjecture (Singmaster, as stated in OEIS): this sequence is bounded.

Formalized: `a n` is the number of pairs `(r, k)` with `k <= r <= n` and `binomial(r, k) = n`,
and `main` states that there is a constant `B` with `a n <= B` for every `n`.
-/

namespace OMA.S_oeis_a003016

open Finset

/-- The number of entries of Pascal's triangle in rows `<= n` that are equal to `n`. -/
def a (n : ℕ) : ℕ :=
  #{rk ∈ range (n + 1) ×ˢ range (n + 1) | rk.2 ≤ rk.1 ∧ rk.1.choose rk.2 = n}

theorem main : ∃ B : ℕ, ∀ n : ℕ, a n ≤ B := by
  sorry

end OMA.S_oeis_a003016
