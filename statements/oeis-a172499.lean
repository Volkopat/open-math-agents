import Mathlib

/-!
# A172499: a(n) = numerator of fraction whose decimal representation is (n).(1)(2)(3)...(n-1)(n)...
with repeating part (1)(2)(3)...(n-1)(n).

Source: https://oeis.org/A172499
Credit: @agchua

Comment line of A172499 (Jaroslav Krizek, Feb 05 2010, the author of the entry), verbatim:
  Sequence of denominators: 9, 33, 333, 9999, 33333, 333333, 9999999, 11111111, 111111111,
  99999999999, 3333333333333, ... Conjecture: this sequence is not equal to the sequence A172498.
A172498 (offset 1): a(n) = denominator of fraction a/b, where gcd(a, b) = 1, whose decimal
representation has the form 0.(1)(2)(3)...(n-1)(n)... with period (1)(2)(3)...(n-1)(n).
Reading: this sequence is the sequence of denominators listed just before the conjecture, that
is, the reduced denominators of the fractions (n).(1)(2)...(n) repeating whose numerators form
A172499. Both sequences have offset 1; the conjecture says that they differ for some n >= 1.
The repeating block (1)(2)...(n) is the decimal concatenation cat(n) of 1, 2, ..., n, which has
len(n) digits and starts with the digit 1, so 0.(1)(2)...(n) repeating equals
cat(n)/(10^len(n) - 1).
-/

namespace OMA.S_oeis_a172499

/-- The decimal concatenation 123...n of the numbers 1, 2, ..., n (cat 0 = 0). -/
def cat : ℕ → ℕ
  | 0 => 0
  | n + 1 => cat n * 10 ^ (Nat.digits 10 (n + 1)).length + (n + 1)

/-- The number of decimal digits of cat n. -/
def len : ℕ → ℕ
  | 0 => 0
  | n + 1 => len n + (Nat.digits 10 (n + 1)).length

/-- The fraction whose decimal representation is (n).(1)(2)...(n) with repeating part
(1)(2)...(n). -/
def x (n : ℕ) : ℚ := (n : ℚ) + (cat n : ℚ) / ((10 : ℚ) ^ len n - 1)

/-- A172499: the numerator of x n. -/
def a (n : ℕ) : ℤ := (x n).num

/-- A172498: the denominator of the reduced fraction whose decimal representation is
0.(1)(2)...(n) with period (1)(2)...(n). -/
def A172498 (n : ℕ) : ℕ := ((cat n : ℚ) / ((10 : ℚ) ^ len n - 1)).den

/-- The sequence of denominators of the fractions of A172499 is not equal to A172498. -/
theorem main : ∃ n : ℕ, 1 ≤ n ∧ (x n).den ≠ A172498 n := by
  sorry

end OMA.S_oeis_a172499
