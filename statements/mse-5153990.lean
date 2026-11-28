import Mathlib

/-!
# Is there a Fibonacci number that is the area of a right triangle with integer sides? (Mohanty–Mohanty Conjecture 4)

Source: https://math.stackexchange.com/questions/5153990/is-there-a-fibonacci-number-that-is-the-area-of-a-right-triangle-with-integer-si
Credit: @mgv27

A positive integer $N$ is a Pythagorean number if it is the area of a right triangle whose
three sides are positive integers, i.e. $N = \tfrac{ab}{2}$ with $a^2 + b^2 = c^2$ for
positive integers $a, b, c$. Conjecture 4 of S. Mohanty and S. P. Mohanty (Pythagorean
Numbers, Fibonacci Quarterly 28 (1990)) states: there is no Pythagorean number in the
Fibonacci sequence. Has this conjecture been proved or disproved?

Formalization notes:
* `main` states the conjecture: no Fibonacci number `Nat.fib n` is a Pythagorean number.
* `IsPythagorean N` requires `N > 0` and positive `a, b, c` with `a² + b² = c²` and
  `a * b = 2 * N`; in particular `F_0 = 0` is not Pythagorean.
* Sanity check: this definition gives exactly `150` Pythagorean numbers below `10^4`,
  matching the count in the question.
-/

namespace OMA.S_mse_5153990

/-- `N` is a Pythagorean number: the area of a right triangle with positive integer sides. -/
def IsPythagorean (N : ℕ) : Prop :=
  0 < N ∧ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 * N

/-- Mohanty–Mohanty Conjecture 4: no Fibonacci number is a Pythagorean number. -/
theorem main : ∀ n : ℕ, ¬ IsPythagorean (Nat.fib n) := by
  sorry

end OMA.S_mse_5153990
