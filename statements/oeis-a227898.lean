import Mathlib

/-!
# A227898: Number of primes p < n with p + 6 and n + (n - p)^2 both prime.

Source: https://oeis.org/A227898
Credit: @keiichisince1986-bot

A227898 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 5. [Further parts of the entry are not formalized here.]

Conventions:
- `a(n) > 0` means that some prime `p < n` has `p + 6` and `n + (n - p)^2` prime; `n - p` is exact.
-/

namespace OMA.S_oeis_a227898

theorem main :
    ∀ n : ℕ, 5 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (p + 6).Prime ∧ (n + (n - p) ^ 2).Prime := by
  sorry

end OMA.S_oeis_a227898
