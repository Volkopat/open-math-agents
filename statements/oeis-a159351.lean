import Mathlib.Data.Nat.Prime.Defs

/-!
# A159351: Smallest prime of the form a^2 + b^2 with 0 < a < b such that a + b = 2n+1.

Source: https://oeis.org/A159351
Credit: @SeanDishman

The sequence has offset 1: for `n ≥ 1`, `a(n)` is the smallest prime of the form `a ^ 2 + b ^ 2`
with `0 < a < b` and `a + b = 2 * n + 1`. The entry conjectures that there is always such a prime,
that is, that `a(n)` exists for every `n ≥ 1`. This is what `main` states.

The range `n ≥ 1` is the offset of the sequence. For `n = 0` the condition `a + b = 1` has no
solution with `0 < a < b`, so the statement would be false there for a trivial reason.

Sanity check of the translation (not part of the file's Lean content): for `n = 1, ..., 19` the
least such primes are `5, 13, 29, 41, 61, 89, 113, 149, 181, 233, 269, 313, 389, 421, 521, 557,
613, 709, 761`, the first terms listed in the entry, and every `n ≤ 2000` has such a prime.
-/

namespace OMA.S_oeis_a159351

/-- **Conjecture (OEIS A159351).** For every `n ≥ 1` there is a prime of the form `a ^ 2 + b ^ 2`
with `0 < a < b` and `a + b = 2 * n + 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ a + b = 2 * n + 1 ∧ (a ^ 2 + b ^ 2).Prime := by
  sorry

end OMA.S_oeis_a159351
