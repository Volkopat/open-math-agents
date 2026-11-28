import Mathlib

/-!
# A249113: Take n and successively add 1, 2, ..., a(n) until reaching a prime for the third time.

Source: https://oeis.org/A249113
Credit: @keiichisince1986-bot

A249113 is the sequence `a(n)` named in the title. The entry states:
Conjecturally (Hardy & Littlewood conjecture F), a(n) exists for all n. - Charles R Greathouse IV,
Oct 21 2014 (The entry attributes this to the Hardy-Littlewood conjecture F; the statement below is the
unconditional claim.)

Conventions:
- After adding `1, 2, …, k` to `n` the value is `n + k(k + 1)/2`. The offset is `1`, so `n ≥ 1`.
- `a(n)` exists means that there are at least three values `k > 0` with `n + k(k + 1)/2` prime.
-/

namespace OMA.S_oeis_a249113

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k₁ k₂ k₃ : ℕ, 0 < k₁ ∧ k₁ < k₂ ∧ k₂ < k₃ ∧
      (n + k₁ * (k₁ + 1) / 2).Prime ∧ (n + k₂ * (k₂ + 1) / 2).Prime ∧
      (n + k₃ * (k₃ + 1) / 2).Prime := by
  sorry

end OMA.S_oeis_a249113
