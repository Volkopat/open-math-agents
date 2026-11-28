import Mathlib

/-!
# A249112: Second smallest k > 0 such that n+(1+2+...+k) is prime.

Source: https://oeis.org/A249112
Credit: @keiichisince1986-bot

A249112 is the sequence `a(n)` named in the title. The entry states:
Conjecturally (Hardy & Littlewood conjecture F), a(n) exists for all n. - Charles R Greathouse IV,
Oct 21 2014 (The entry attributes this to the Hardy-Littlewood conjecture F; the statement below is the
unconditional claim.)

Conventions:
- `1 + 2 + … + k = k(k + 1)/2`. The offset is `1`, so `n ≥ 1`.
- `a(n)` exists means that there are at least two values `k > 0` with `n + k(k + 1)/2` prime.
-/

namespace OMA.S_oeis_a249112

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ k₁ < k₂ ∧
      (n + k₁ * (k₁ + 1) / 2).Prime ∧ (n + k₂ * (k₂ + 1) / 2).Prime := by
  sorry

end OMA.S_oeis_a249112
