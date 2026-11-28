import Mathlib

/-!
# A083452: a(n) = (n times concatenation of n - n^n) divided by n, or a(n) = A083451(n)/n.

Source: https://oeis.org/A083452
Credit: @bnb9001

Offset 1: 0, 9, 102, 1047, 10486, ... The n-fold decimal concatenation of n is the number whose
digits are those of n repeated n times (written here with `Nat.digits`, which is little-endian,
so repeating the digit list repeats the block).

Conjecture: all the terms are positive for n > 1 (n times concatenation of n with itself > n^n).
-/

namespace OMA.S_oeis_a083452

/-- The base-10 concatenation of `n` with itself `n` times. -/
def concatRep (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (List.flatten (List.replicate n (Nat.digits 10 n)))

/-- A083452: `(concatRep n - n^n) / n`. -/
def a (n : ℕ) : ℤ := ((concatRep n : ℤ) - (n : ℤ) ^ n) / n

/-- The conjecture: every term is positive for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a083452
