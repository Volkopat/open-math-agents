import Mathlib

/-!
# A247672: Least integer m > 0 with pi(m*n) = phi(m) + phi(n), where pi(.) is the prime-counting function and phi(.) is Euler's totient function.

Source: https://oeis.org/A247672
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` with `π(m n) = φ(m) + φ(n)` (`a(1) = 6`, `a(4) = 23`). The
entry conjectures (Zhi-Wei Sun):

  a(n) exists for every n > 0.

`main` states that for every `n ≥ 1` some `m > 0` has `π(m n) = φ(m) + φ(n)`. `π(x)` is `Nat.primeCounting x`, the number of primes `≤ x`. `φ` is
`Nat.totient`.
-/

namespace OMA.S_oeis_a247672


/-- The conjecture in OEIS A247672: for every `n ≥ 1` there is `m > 0` with `π(m n) = φ(m) + φ(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ Nat.primeCounting (m * n) = Nat.totient m + Nat.totient n := by
  sorry

end OMA.S_oeis_a247672
