import Mathlib

/-!
# A158509: Prime(n-1) such that prime(n-1)+5 is square and equal to prime(n+1)-1

Source: https://oeis.org/A158509
Credit: @xor2k

Formalizes the OEIS A158509 conjecture: If the condition holds, prime(n-1) and prime(n) are
twin primes of the form 10k+1 and 10k+3. I.e., the last digits of the primes are 1 and 3.

Conventions:
* `prime k` is the OEIS `prime(k)`, the `k`-th prime with `prime 1 = 2`; in Lean it is
  `Nat.nth Nat.Prime (k - 1)` (Mathlib indexes primes from `0`). It is used only for `k ≥ 1`.
* The condition on `n` (with `n ≥ 2`, so that `prime(n-1)` is defined) is: `prime(n-1) + 5`
  is a perfect square and `prime(n-1) + 5 = prime(n+1) - 1`.
* Twin primes means `prime n = prime (n-1) + 2`; the forms 10k+1 and 10k+3 mean
  `prime (n-1) % 10 = 1` and `prime n % 10 = 3`.
-/

namespace OMA.S_oeis_a158509

/-- The OEIS `prime(k)`: the `k`-th prime, `prime 1 = 2`, `prime 2 = 3`, ... -/
noncomputable def prime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- If `prime(n-1) + 5` is a square equal to `prime(n+1) - 1`, then `prime(n-1)` and `prime(n)`
are twin primes ending in the digits 1 and 3. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n → IsSquare (prime (n - 1) + 5) → prime (n - 1) + 5 = prime (n + 1) - 1 →
      prime n = prime (n - 1) + 2 ∧ prime (n - 1) % 10 = 1 ∧ prime n % 10 = 3 := by
  sorry

end OMA.S_oeis_a158509
