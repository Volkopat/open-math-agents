import Mathlib

/-!
# A179256: a(n) is the smallest prime q such that (q-p)/(r-q) = n, where p<q<r are consecutive primes (or 0 if none exist).

Source: https://oeis.org/A179256
Credit: @keiichisince1986-bot

A179256 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n)>0 for n >= 1.

Conventions:
- Primes are indexed from `0`: `Nat.nth Nat.Prime i`. Three consecutive primes are `p = Nat.nth Nat.Prime (i - 1)`,
  `q = Nat.nth Nat.Prime i`, `r = Nat.nth Nat.Prime (i + 1)` with `i ≥ 1`; their differences are exact.
- `(q - p)/(r - q) = n` is written `q - p = n (r - q)`.
-/

namespace OMA.S_oeis_a179256

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, 1 ≤ i ∧
      Nat.nth Nat.Prime i - Nat.nth Nat.Prime (i - 1) = n * (Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i) := by
  sorry

end OMA.S_oeis_a179256
