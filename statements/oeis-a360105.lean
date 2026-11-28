import Mathlib

/-!
# A360105: Numbers k such that sigma_2(k^2 + 1) == 0 (mod k)

Source: https://oeis.org/A360105

Conjecture (OEIS A360105):
The sequence of positive integers `k` dividing `σ_2(k^2 + 1)` contains infinitely many
Fibonacci numbers (cf. A360107).

Conventions:
- Offset: `1`; `k ≥ 1`.
- Fibonacci numbers in the sequence include `1, 2, 5, 13, 34, 89, 233, 610, 4181, ...`.
- `σ_2(m)` is defined directly as `∑ d ∈ m.divisors, d ^ 2`.
-/

namespace OMA.S_oeis_a360105

/-- Sum of squares of positive divisors `σ_2(m)` of `m : ℕ`. -/
def sigma2 (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors, d ^ 2

/-- The set of positive integers `k` dividing `σ_2(k^2 + 1)` (OEIS A360105). -/
def S : Set ℕ :=
  {k : ℕ | 1 ≤ k ∧ k ∣ sigma2 (k ^ 2 + 1)}

/-- Conjecture: `S` contains infinitely many Fibonacci numbers. -/
theorem main : Set.Infinite {k : ℕ | k ∈ S ∧ ∃ n : ℕ, k = Nat.fib n} := by
  sorry

end OMA.S_oeis_a360105
