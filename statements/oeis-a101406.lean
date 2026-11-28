import Mathlib

/-!
# A101406: a(n) = least k such that k^n*(k^n-1)-1 is prime.

Source: https://oeis.org/A101406
Credit: @keiichisince1986-bot

A101406 is the sequence `a(n)` named in the title. The entry states:
Under the Bunyakovsky conjecture, a(n) exists for every n. [Charles R Greathouse IV, Dec 27 2011]
(The statement below is the unconditional claim.)

Conventions:
- The offset is `1`, so `n ≥ 1`. For `k ≤ 1` the value is negative and its natural-number truncation `0`
  is not prime, so only `k ≥ 2` can count, as in the data (`a(n) ≥ 2`).
-/

namespace OMA.S_oeis_a101406

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (k ^ n * (k ^ n - 1) - 1).Prime := by
  sorry

end OMA.S_oeis_a101406
