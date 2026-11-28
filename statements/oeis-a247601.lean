import Mathlib

/-!
# A247601: Least positive integer m with pi(m*n) = phi(m).

Source: https://oeis.org/A247601
Credit: @sntntHb

Data: 2, 1, 13, 31, 73, 181, 443, 2249, 238839, 6473, ...

Here `pi` is the prime-counting function and `phi` is Euler's totient function.

Conjecture (Zhi-Wei Sun, stated on the OEIS page): `a(n)` exists for any `n > 0`, i.e. for
every `n ≥ 1` there is a positive integer `m` with `pi(m*n) = phi(m)`.
-/

namespace OMA.S_oeis_a247601

theorem main :
    ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ Nat.primeCounting (m * n) = Nat.totient m := by
  sorry

end OMA.S_oeis_a247601
