import Mathlib

/-!
# A214794: Numbers n such that n - 5 = A214793(n)

Source: https://oeis.org/A214794
Author: Art DuPre (2012)

Conjecture (OEIS A214794):
Let `A214793(n)` be the least integer `k ≥ 2` such that `n` divides `Fib(k - 1) + 13`
(or `0` if no such `k` exists). Then `28` is the only nonprime integer `n` satisfying
`n - 5 = A214793(n)`.

Conventions:
- Since `A214793(n) ≥ 2` whenever it is nonzero, `n - 5 = A214793(n)` implies `n ≥ 7`.
- First terms of A214794: `7, 13, 23, 28, 37, 43, 67, 73, 83, 127, 137, ...`.
- For `n = 28`, `k = 23` is the least `k ≥ 2` with `28 ∣ Fib(22) + 13 = 17724`.
-/

namespace OMA.S_oeis_a214794

/-- Predicate stating that `k` is the least integer `≥ 2` such that `n ∣ Fib(k - 1) + 13`
(OEIS A214793). -/
def IsA214793 (n k : ℕ) : Prop :=
  IsLeast {j : ℕ | 2 ≤ j ∧ n ∣ Nat.fib (j - 1) + 13} k

/-- Conjecture: `28` is the only nonprime in A214794. -/
theorem main :
    ∀ n : ℕ, 7 ≤ n → IsA214793 n (n - 5) → n ≠ 28 → Nat.Prime n := by
  sorry

end OMA.S_oeis_a214794
