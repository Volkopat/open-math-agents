import Mathlib

/-!
# A144590: odd numbers as a prime plus a positive pronic number

Source: https://oeis.org/A144590

A144590 (offset 0): `a(n)` is the number of ordered ways of writing `2n+1 = i + j`, where `i` is a
prime and `j` is of the form `k*(k+1)` with `k > 0`.

Conjecture (Zhi-Wei Sun, posting to the Number Theory Mailing List, Mar 23 2008, as recorded in
the entry by N. J. A. Sloane, Jan 15 2009): `a(n) > 0` for `n ≥ 2`. In other words, every odd
integer `2n+1 ≥ 5` is the sum of a prime and twice a positive triangular number. The entry notes
that no counterexample exists below `10^10` (D. S. McNeil).

Conventions:
- The index `n` is the OEIS index (offset 0), so `a 0 = 0`, `a 1 = 0`, `a 2 = 1`, `a 4 = 2`.
- A way of writing `2n+1 = i + j` is determined by `k`, since `k ↦ k*(k+1)` is injective on the
  positive integers and `i = 2n+1 - j`. So `a n` counts the `k > 0` with `k*(k+1) ≤ 2n+1` and
  `2n+1 - k*(k+1)` prime; any such `k` is at most `2n+1`, so the search range
  `Finset.range (2n+2)` loses nothing.
- Everything is in `ℕ`; the bound `k*(k+1) ≤ 2n+1` is kept explicit so the truncated subtraction
  is a genuine subtraction.
-/

namespace OMA.S_oeis_a144590

/-- A144590: the number of `k > 0` such that `2n+1 - k*(k+1)` is a (nonnegative) prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 2)).filter
    (fun k => 0 < k ∧ k * (k + 1) ≤ 2 * n + 1 ∧ Nat.Prime (2 * n + 1 - k * (k + 1)))).card

theorem main : ∀ n : ℕ, 2 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a144590
