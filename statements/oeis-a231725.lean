import Mathlib

/-!
# A231725: Least positive integer k < n such that n + k + 2^k is prime, or 0 if such an integer k does not exist.

Source: https://oeis.org/A231725
Credit: @keiichisince1986-bot

A231725 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 3. (Verified for n up to 2*10^6.)

Conventions:
- `a(n) > 0` means that some positive integer `k < n` makes `n + k + 2^k` prime (then the least
  such `k` is positive).
-/

namespace OMA.S_oeis_a231725

theorem main :
    ∀ n : ℕ, 3 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (n + k + 2 ^ k).Prime := by
  sorry

end OMA.S_oeis_a231725
