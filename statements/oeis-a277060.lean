import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

/-!
# A277060: a(n) = (1/2) * ∑_{k=0}^n (C(n, k) * C(n + k, k + 1))^2

Source: https://oeis.org/A277060

`a(n) = (1/2) * ∑_{k=0}^n (binomial(n, k) * binomial(n + k, k + 1))^2` for `n ≥ 0`
(`0, 1, 28, 729, 19376, 529575, ...`).

Peter Bala (Mar 22 2023) conjectured in OEIS A277060:
1. `a(p - 1) ≡ 1 (mod p^4)` for all primes `p ≥ 5`.
2. `a(p^2 - 1) ≡ 1 (mod p^5)` for all primes `p ≥ 3`.
-/

namespace OMA.S_oeis_a277060

/-- `a n` is the `n`-th term of OEIS A277060. -/
def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.range (n + 1), (n.choose k * (n + k).choose (k + 1)) ^ 2) / 2

/-- Peter Bala's supercongruence conjectures for OEIS A277060:
1. `a(p - 1) ≡ 1 (mod p^4)` for all primes `p ≥ 5`.
2. `a(p^2 - 1) ≡ 1 (mod p^5)` for all primes `p ≥ 3`. -/
theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → a (p - 1) ≡ 1 [MOD p ^ 4]) ∧
    (∀ p : ℕ, p.Prime → 3 ≤ p → a (p ^ 2 - 1) ≡ 1 [MOD p ^ 5]) := by
  sorry

end OMA.S_oeis_a277060
