import Mathlib

/-!
# A219842: Number of ways to write n as x+y (0<x<=y) with 2x*y+1 prime.

Source: https://oeis.org/A219842
Credit: @keiichisince1986-bot

A219842 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n)>0 for all n>1. Moreover, any integer n>357 can be written as x+y (x>0, y>0)
with 2x*y+1 and 2x*y-1 twin primes.

Conventions:
- `a(n) > 0` means that there are integers `0 < x ≤ y` with `n = x + y` and `2xy + 1` prime.
- The conjecture has two parts, and `main` is their conjunction. In the second part, `2xy - 1`
  and `2xy + 1` being twin primes means that both are prime (here `2xy ≥ 2`, so `2xy - 1` is not
  truncated).
-/

namespace OMA.S_oeis_a219842

theorem main :
    (∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ n = x + y ∧ (2 * x * y + 1).Prime) ∧
      ∀ n : ℕ, 357 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧ (2 * x * y + 1).Prime ∧
        (2 * x * y - 1).Prime := by
  sorry

end OMA.S_oeis_a219842
