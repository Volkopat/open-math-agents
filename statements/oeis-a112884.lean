import Mathlib

/-!
# A112884: the number of bits of binomial(2^n, 2^(n-1)) is 2^n - floor(n/2)

Source: https://oeis.org/A112884
Credit: @ivillar

Status: known result: the entry records that the conjectured formula is true (Sela Fried, Oct 03 2024).

A112884 (offset 0) is the number of bits required to represent binomial(2^n, 2^(n-1));
data 1, 2, 3, 7, 14, 30, 61, 125, 252, 508, 1019, ...

Conjecture (in the comments of A112884): the sequence appears to be equal to 2^n - floor(n/2).
Sela Fried (Oct 03 2024) records in the entry that the conjectured formula is true.

Formalization: the number of bits of a positive integer is the length of its list of binary
digits. For n = 0 the natural-number exponent n - 1 is 0, so the term is the number of bits of
binomial(1, 1) = 1, which is 1 = a(0) as in the entry. The formula is stated for every n ≥ 0 with
natural-number subtraction and division (2^n > floor(n/2) always).
-/

namespace OMA.S_oeis_a112884

/-- a(n): the number of binary digits of binomial(2^n, 2^(n-1)). -/
def a (n : ℕ) : ℕ := (Nat.digits 2 (Nat.choose (2 ^ n) (2 ^ (n - 1)))).length

/-- The conjectured formula a(n) = 2^n - floor(n/2). -/
theorem main : ∀ n : ℕ, a n = 2 ^ n - n / 2 := by
  sorry

end OMA.S_oeis_a112884
