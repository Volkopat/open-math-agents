import Mathlib

/-!
# A079450: a(n) = 2^(n-1)*u(n) where u(1)=1 and u(n) = frac(3/2*u(n-1)) + 1.

Source: https://oeis.org/A079450 (Benoit Cloitre). Related: https://oeis.org/A077468
Credit: @Squee451

Data (offset 1): 1, 3, 5, 15, 29, 55, 101, 175, 269, 807, 1397, 2143, 6429, 11095, 16901, 50703, ...

The entry's formula line: a(n+1) <= 3*a(n). Conjecture: a(n+1) = 3*a(n) if and only if n is a greedy
power of (2/3) (i.e. n is in A077468).

A077468 (offset 1) is 1, 3, 9, 12, 15, 17, 27, 34, 39, 46, 49, 52, ...: "Greedy powers of (2/3):
Sum_{n>=1} (2/3)^a(n) = 1", and its comment defines them: "The n-th greedy power of x, when
0.5 < x < 1, is the smallest integer exponent a(n) that does not cause the power series
Sum_{k=1..n} x^a(k) to exceed unity."

Conventions.
* A079450 has offset 1. `u 0 = 0` below is a placeholder that is not part of the sequence; `u` and `a`
  are rational-valued (every `a n` is in fact an integer). `Int.fract` is the fractional part.
* Greedy powers are positive exponents (the data starts 1, 3, 9; exponent 0 is not allowed).
  `Greedy l` says that the list `l` is an initial segment of A077468, in order: each new term is the
  least positive integer `k` for which the sum of the powers already chosen plus `(2/3)^k` is at
  most 1. This is the entry's definition word for word; nothing about monotonicity is assumed.
  A number is a greedy power when it occurs in such a list.
-/

namespace OMA.S_oeis_a079450

/-- `u 1 = 1` and `u n = frac((3/2) * u (n-1)) + 1` for `n ≥ 2`. -/
def u : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => Int.fract ((3 / 2 : ℚ) * u (n + 1)) + 1

/-- A079450: `a n = 2^(n-1) * u n`. -/
def a (n : ℕ) : ℚ := 2 ^ (n - 1) * u n

/-- `Greedy l`: the list `l` consists of the first greedy powers of 2/3 (A077468), in order. Each new
exponent is the smallest positive integer that does not make the sum of the powers exceed 1. -/
inductive Greedy : List ℕ → Prop
  | nil : Greedy []
  | snoc (l : List ℕ) (e : ℕ) : Greedy l →
      IsLeast {k : ℕ | 1 ≤ k ∧ (l.map fun j => (2 / 3 : ℚ) ^ j).sum + (2 / 3 : ℚ) ^ k ≤ 1} e →
      Greedy (l ++ [e])

/-- `n` is a greedy power of 2/3, i.e. a term of A077468. -/
def IsGreedyPower (n : ℕ) : Prop := ∃ l : List ℕ, Greedy l ∧ n ∈ l

/-- For every `n ≥ 1`: `a (n+1) = 3 * a n` if and only if `n` is a greedy power of 2/3. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a (n + 1) = 3 * a n ↔ IsGreedyPower n) := by
  sorry

end OMA.S_oeis_a079450
