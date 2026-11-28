import Mathlib

/-!
# A172505: a(n) = numerator of fraction a/b, where gcd(a, b) = 1, whose decimal representation has the form (1)(2)(3)...(n-1)(n).(1)(2)(3)...(n-1)(n)... with period (1)(2)(3)...(n-1)(n).

Source: https://oeis.org/A172505
Credit: @agchua

Comment of A172505 (the entry is by Jaroslav Krizek, Feb 05 2010):
  Sequence of denominators: 9, 33, 333, 9999, 33333, 333333, ... Conjecture: this sequence is not
  equal to the sequence A172498.
Here C(n) = 123...n is the concatenation of the decimal expansions of 1, ..., n, and L(n) is its
number of digits. The number of the entry is x(n) = C(n) + C(n)/(10^L(n) - 1), whose decimal
expansion is C(n).C(n)C(n)... ; A172505(n) is the numerator of x(n), and b(n) below is its
denominator: the sequence of denominators of the comment. A172498(n) is, by its name, the
denominator of 0.C(n)C(n)... = C(n)/(10^L(n) - 1). Both sequences have offset 1. The statement
is the comment as printed: the listed denominators, and the conjecture that the two sequences
differ at some n >= 1.
-/

namespace OMA.S_oeis_a172505

/-- C n: the concatenation 123...n of the decimal expansions of 1, ..., n (and C 0 = 0). -/
def C : ℕ → ℕ
  | 0 => 0
  | n + 1 => C n * 10 ^ (Nat.digits 10 (n + 1)).length + (n + 1)

/-- L n: the number of decimal digits of C n. -/
def L (n : ℕ) : ℕ := (Nat.digits 10 (C n)).length

/-- x n = C(n) + C(n)/(10^L(n) - 1), the number with decimal expansion C(n).C(n)C(n)... -/
def x (n : ℕ) : ℚ := (C n : ℚ) + (C n : ℚ) / ((10 : ℚ) ^ L n - 1)

/-- A172505(n): the numerator of x n. -/
def a (n : ℕ) : ℤ := (x n).num

/-- The sequence of denominators of A172505: the denominator of x n. -/
def b (n : ℕ) : ℕ := (x n).den

/-- A172498(n): the denominator of 0.C(n)C(n)... = C(n)/(10^L(n) - 1). -/
def A172498 (n : ℕ) : ℕ := ((C n : ℚ) / ((10 : ℚ) ^ L n - 1)).den

/-- The comment: the denominators begin 9, 33, 333, 9999, 33333, 333333, and (the conjecture)
the sequence of denominators is not equal to A172498. -/
theorem main : (b 1 = 9 ∧ b 2 = 33 ∧ b 3 = 333 ∧ b 4 = 9999 ∧ b 5 = 33333 ∧ b 6 = 333333) ∧
    ∃ n : ℕ, 1 ≤ n ∧ b n ≠ A172498 n := by
  sorry

end OMA.S_oeis_a172505
