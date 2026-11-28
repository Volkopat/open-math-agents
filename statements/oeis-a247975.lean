import Mathlib

/-!
# A247975: Least positive integer m such that m + n divides prime(m)^2 + prime(n)^2.

Source: https://oeis.org/A247975
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` such that `m + n` divides `prime(m)^2 + prime(n)^2`, where
`prime(k)` is the `k`-th prime (`a(1) = 1`, `a(3) = 15479`). The entry conjectures (Zhi-Wei Sun):

  a(n) exists for any n > 0.

`main` states that for every `n ≥ 1` some `m > 0` works. `prime k` is `Nat.nth Nat.Prime (k - 1)`.
-/

namespace OMA.S_oeis_a247975

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture in OEIS A247975: for every `n ≥ 1` there is `m > 0` with
`m + n ∣ prime(m)^2 + prime(n)^2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ m + n ∣ prime m ^ 2 + prime n ^ 2 := by
  sorry

end OMA.S_oeis_a247975
