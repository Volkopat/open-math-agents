import Mathlib

/-!
# A110278: Numbers n such that the perfect deficiency of n and n + 1 are both squares

Source: https://oeis.org/A110278

Conjecture (OEIS A110278):
There are infinitely many positive integers `n` such that both `A109883(n)` and
`A109883(n + 1)` are perfect squares, where `A109883(m)` is the greedy perfect
deficiency of `m` (the remainder after greedily subtracting the proper divisors of `m`
from largest to smallest whenever possible).

Conventions:
- Offset: `1`; first terms: `1, 4, 5, 16, 17, 36, 37, 100, 101, 196, 197, 256, 257, ...`.
- For `m = 50`, the proper divisors in decreasing order are `25, 10, 5, 2, 1`, giving
  `50 → 25 → 15 → 10 → 8 → 7`, so `A109883(50) = 7`.
-/

namespace OMA.S_oeis_a110278

/-- Greedy perfect deficiency of `m : ℕ` (OEIS A109883): start with `m` and subtract
each proper divisor of `m` in decreasing order whenever it does not exceed the
current remainder. -/
def greedyDeficiency (m : ℕ) : ℕ :=
  (((List.range m).filter (fun d => decide (1 ≤ d ∧ d ∣ m))).reverse).foldl
    (fun rem d => if d ≤ rem then rem - d else rem) m

/-- Predicate stating that `k : ℕ` is a perfect square. -/
def IsNatSquare (k : ℕ) : Prop :=
  ∃ r : ℕ, k = r ^ 2

/-- The set of positive integers `n` whose greedy perfect deficiency and that of `n + 1`
are both squares (OEIS A110278). -/
def S : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ IsNatSquare (greedyDeficiency n) ∧ IsNatSquare (greedyDeficiency (n + 1))}

/-- Conjecture: the sequence A110278 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a110278
