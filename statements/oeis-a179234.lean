import Mathlib

/-!
# A179234: a(n) is the smallest prime q such that, for the previous prime p and the following prime r, the fraction (r-q)/(q-p) has denominator n in lowest terms.

Source: https://oeis.org/A179234
Credit: @keiichisince1986-bot

A179234 is the sequence `a(n)` named in the title. The entry states:
The conjecture that a(n) exists for every n is a weaker conjecture than a related one in the comment to
A179210. (We formalize: a(n) exists for every n >= 1.)

Conventions:
- Primes are indexed from `0`: `Nat.nth Nat.Prime i`. Three consecutive primes are `p = Nat.nth Nat.Prime (i - 1)`,
  `q = Nat.nth Nat.Prime i`, `r = Nat.nth Nat.Prime (i + 1)` with `i ≥ 1`; their differences are exact.
- The fraction is computed in `ℚ`; `den` is its denominator in lowest terms.
-/

namespace OMA.S_oeis_a179234

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, 1 ≤ i ∧
      (((Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i : ℕ) : ℚ) /
        ((Nat.nth Nat.Prime i - Nat.nth Nat.Prime (i - 1) : ℕ) : ℚ)).den = n := by
  sorry

end OMA.S_oeis_a179234
