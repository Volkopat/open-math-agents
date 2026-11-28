import Mathlib

/-!
# A247602: Least positive integer m with pi(m*n) = phi(m+n), where pi(.) is the prime-counting function and phi(.) is Euler's totient function.

Source: https://oeis.org/A247602
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` with `π(m n) = φ(m + n)` (`a(1) = 3`, `a(4) = 91`). The entry
conjectures (Zhi-Wei Sun):

  a(n) exists for any n > 0.

`main` states that for every `n ≥ 1` some `m > 0` has `π(m n) = φ(m + n)`. `π(x)` is `Nat.primeCounting x`, the number of primes `≤ x`. `φ` is
`Nat.totient`.
-/

namespace OMA.S_oeis_a247602


/-- The conjecture in OEIS A247602: for every `n ≥ 1` there is `m > 0` with `π(m n) = φ(m + n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ Nat.primeCounting (m * n) = Nat.totient (m + n) := by
  sorry

end OMA.S_oeis_a247602
