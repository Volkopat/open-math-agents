import Mathlib

/-!
# A214796: Numbers n such that n - 8 = A214795(n)

Source: https://oeis.org/A214796
Author: Art DuPre (2012)

Conjecture (OEIS A214796):
Let `A214795(n)` be the least integer `k ≥ 2` such that `n` divides `Fib(k - 1) + 21`
(or `0` if no such `k` exists). Then every integer `n` satisfying `n - 8 = A214795(n)`
is prime.

Conventions:
- Since `A214795(n) ≥ 2` whenever it is nonzero, `n - 8 = A214795(n)` implies `n ≥ 10`.
- First terms of A214796: `19, 31, 59, 71, 79, ...`.
- For `n = 19`, `k = 11` is the least `k ≥ 2` with `19 ∣ Fib(10) + 21 = 76`.
-/

namespace OMA.S_oeis_a214796

/-- Predicate stating that `k` is the least integer `≥ 2` such that `n ∣ Fib(k - 1) + 21`
(OEIS A214795). -/
def IsA214795 (n k : ℕ) : Prop :=
  IsLeast {j : ℕ | 2 ≤ j ∧ n ∣ Nat.fib (j - 1) + 21} k

/-- Conjecture: every term of A214796 is prime. -/
theorem main :
    ∀ n : ℕ, 10 ≤ n → IsA214795 n (n - 8) → Nat.Prime n := by
  sorry

end OMA.S_oeis_a214796
