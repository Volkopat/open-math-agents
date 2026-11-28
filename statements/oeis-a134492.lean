import Mathlib

/-!
# A134492: a(n) = Fibonacci(6*n).

Source: https://oeis.org/A134492
Credit: @avivorly

A134492 (offset 0): `a(n) = F(6n)`: 0, 8, 144, 2584, 46368, ...

Conjecture (Felix Huber, Nov 03 2023): For `n >= 2`, the terms of this sequence are exactly those
Fibonacci numbers which are the sum of the three numbers of a Pythagorean triple (checked up to F(80)).

That is: the set `{F(6n) : n ≥ 2}` equals the set of Fibonacci numbers `F(j)` that are the sum `a + b + c`
of a Pythagorean triple `(a, b, c)`, and the conjecture is stated as this equality of sets.

Conventions:
- `Nat.fib` is Mathlib's Fibonacci sequence (`F(0) = 0`, `F(1) = 1`).
- A Pythagorean triple is a triple of positive integers `(a, b, c)` with `a^2 + b^2 = c^2` (not required
  to be primitive, as in the usual definition).
-/

namespace OMA.S_oeis_a134492

/-- `x` is the sum of the three numbers of a Pythagorean triple. -/
def IsPythagoreanSum (x : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a + b + c = x

theorem main :
    {x : ℕ | ∃ n : ℕ, 2 ≤ n ∧ x = Nat.fib (6 * n)} =
      {x : ℕ | (∃ j : ℕ, x = Nat.fib j) ∧ IsPythagoreanSum x} := by
  sorry

end OMA.S_oeis_a134492
