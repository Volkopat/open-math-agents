import Mathlib

/-!
# A179210: a(n) is the smallest prime q such that (r-q)/(q-p) = n, where p<q<r are consecutive primes (or 0 if no such prime exists).

Source: https://oeis.org/A179210
Credit: @keiichisince1986-bot

A179210 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n >= 1.

Conventions:
- Three consecutive primes are `p_i < p_(i+1) < p_(i+2)`, where `p_i = Nat.nth Nat.Prime i` is the
  `i`-th prime counting from `p_0 = 2`.
- `a(n) > 0` means that some three consecutive primes `p < q < r` satisfy `(r - q)/(q - p) = n`,
  i.e. `r - q = n (q - p)` (the subtractions are exact, as the primes increase).
-/

namespace OMA.S_oeis_a179210

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, Nat.nth Nat.Prime (i + 2) - Nat.nth Nat.Prime (i + 1) =
        n * (Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i) := by
  sorry

end OMA.S_oeis_a179210
