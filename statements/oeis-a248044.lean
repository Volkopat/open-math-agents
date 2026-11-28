import Mathlib

/-!
# A248044: Least positive integer m such that m + n divides pi(m)^2 + pi(n)^2, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A248044
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` such that `m + n` divides `π(m)^2 + π(n)^2` (`a(1) = 1`:
`2 ∣ 0 + 0`). The entry conjectures (Zhi-Wei Sun):

  a(n) exists for any n > 0.

`main` states that for every `n ≥ 1` some `m > 0` works. `π(x)` is `Nat.primeCounting x`, the number of primes `≤ x`.
-/

namespace OMA.S_oeis_a248044


/-- The conjecture in OEIS A248044: for every `n ≥ 1` there is `m > 0` with
`m + n ∣ π(m)^2 + π(n)^2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ m + n ∣ Nat.primeCounting m ^ 2 + Nat.primeCounting n ^ 2 := by
  sorry

end OMA.S_oeis_a248044
