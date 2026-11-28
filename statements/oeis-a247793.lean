import Mathlib

/-!
# A247793: Least integer m > 0 such that pi(m*n) divides prime(m) + prime(n), where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A247793
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` such that `π(m n)` divides `prime(m) + prime(n)`, where
`prime(k)` is the `k`-th prime (`a(1) = 2`: `π(2) = 1` divides `3 + 2`). The entry conjectures
(Zhi-Wei Sun):

  a(n) exists for any n > 0.

`main` states that for every `n ≥ 1` some `m > 0` works. `π(x)` is `Nat.primeCounting x`, the number of primes `≤ x`. `prime k` is
`Nat.nth Nat.Prime (k - 1)`. (For `m = n = 1`, `π(1) = 0` and `0 ∣ 4` is false, matching the
convention that `0` divides only `0`.)
-/

namespace OMA.S_oeis_a247793

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture in OEIS A247793: for every `n ≥ 1` there is `m > 0` with
`π(m n) ∣ prime(m) + prime(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ Nat.primeCounting (m * n) ∣ prime m + prime n := by
  sorry

end OMA.S_oeis_a247793
