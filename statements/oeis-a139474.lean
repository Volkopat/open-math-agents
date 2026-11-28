import Mathlib

/-!
# A139474: a(n) = ((2*sqrt(2) + 3)^(2^(prime(n) - 1) - 1) - (3 - 2*sqrt(2))^(2^(prime(n) - 1) - 1))/(4*sqrt(2)).

Source: https://oeis.org/A139474
Credit: @luciusacarr

The entry (offset 1, data 1, 35, 53789260175, ...) records one conjecture (Kenneth J Ramsey,
May 16 2006, see A001109): a(n) is divisible by 2^prime(n) - 1 if and only if 2^prime(n) - 1 is a
Mersenne prime.

Reading of the source:
* `prime(n)` is the n-th prime with `prime(1) = 2`; in Lean `prime(n) = Nat.nth Nat.Prime (n - 1)`.
  The offset is 1, so the conjecture is about every `n ≥ 1`.
* Put `N = 2^(prime(n) - 1) - 1`. With `b(k) = ((3 + 2√2)^k - (3 - 2√2)^k)/(4√2)` we have
  `b(0) = 0`, `b(1) = 1`, and `b(k + 2) = 6 b(k + 1) - b(k)`, because `3 ± 2√2` are the roots of
  `x^2 - 6x + 1`. So `b` is the integer sequence A001109 (0, 1, 6, 35, 204, ...), defined below by
  this recurrence, and `a(n) = b(N)`. (E.g. `n = 2`: `prime(2) = 3`, `N = 3`, `a(2) = b(3) = 35`.)
* Since `prime(n)` is prime, "2^prime(n) - 1 is a Mersenne prime" means "2^prime(n) - 1 is prime".
* The conjecture: for every `n ≥ 1`, `(2^prime(n) - 1) ∣ a(n)` if and only if `2^prime(n) - 1` is
  prime.
-/

namespace OMA.S_oeis_a139474

/-- A001109: `b 0 = 0`, `b 1 = 1`, `b (k + 2) = 6 b (k + 1) - b k`,
i.e. `b k = ((3 + 2√2)^k - (3 - 2√2)^k)/(4√2)`. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => 6 * b (k + 1) - b k

/-- The `n`-th prime, `prime(1) = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `a(n) = b(2^(prime(n) - 1) - 1)`. -/
noncomputable def a (n : ℕ) : ℤ := b (2 ^ (prime n - 1) - 1)

theorem main :
    ∀ n : ℕ, 1 ≤ n → ((2 ^ prime n - 1 : ℤ) ∣ a n ↔ Nat.Prime (2 ^ prime n - 1)) := by
  sorry

end OMA.S_oeis_a139474
