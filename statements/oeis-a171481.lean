import Mathlib

/-!
# A171481: a(n) = a(a(n-1)) + a(n - a(n-1) - 2) with a(0) = 0, a(1) = a(2) = 1.

Source: https://oeis.org/A171481
Credit: @rpabani

Conjecture 1 in OEIS A171481: a(n) - a(n-1) = 0 or 1.

The statement is made about any sequence of natural numbers with these initial values that
satisfies the recurrence for n >= 3. The index n - a(n-1) - 2 is written with natural-number
subtraction; in the sequence of the source it is never negative as far as computed (checked for
n < 20000), so no truncation occurs there. Conjecture 2 of the source, on the limit of a(n)/n, is a
separate statement and is not included.
-/

namespace OMA.S_oeis_a171481

theorem main : ∀ a : ℕ → ℕ, a 0 = 0 → a 1 = 1 → a 2 = 1 →
    (∀ n : ℕ, 3 ≤ n → a n = a (a (n - 1)) + a (n - a (n - 1) - 2)) →
    ∀ n : ℕ, 1 ≤ n → a n = a (n - 1) ∨ a n = a (n - 1) + 1 := by
  sorry

end OMA.S_oeis_a171481
