import Mathlib

/-!
# A367182: Primes of the form (k-th primorial) - (k + 1)-st prime

Source: https://oeis.org/A367182

Conjecture (OEIS A367182):
There are infinitely many primes of the form `p_k# - prime(k + 1)`.

Conventions:
- Offset: `1`; first terms: `23` (`k = 3`: `30 - 7`), `199` (`k = 4`: `210 - 11`),
  `2297` (`k = 5`: `2310 - 13`), `30013` (`k = 6`), `9699667` (`k = 8`), ...
- `primorial k` is the product of the first `k` primes (`Nat.nth Nat.Prime 0` through
  `Nat.nth Nat.Prime (k - 1)`), and `Nat.nth Nat.Prime k` is the `(k + 1)`-st prime.
- Including `Nat.nth Nat.Prime k < primorial k` avoids `ℕ` subtraction underflow for `k = 1`.
-/

namespace OMA.S_oeis_a367182

/-- The `k`-th primorial `p_k#`, product of the first `k` primes. -/
noncomputable def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- The set of primes of the form `p_k# - prime(k + 1)` (OEIS A367182). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧
    ∃ k : ℕ, 1 ≤ k ∧ Nat.nth Nat.Prime k < primorial k ∧
      p = primorial k - Nat.nth Nat.Prime k}

/-- Conjecture: there are infinitely many primes of the form `p_k# - prime(k + 1)`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a367182
