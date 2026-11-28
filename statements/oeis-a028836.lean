import Mathlib

/-!
# A028836: Iterated sum of digits of n is a power of 2

Source: https://oeis.org/A028836
Credit: @ivillar

The terms, with offset 1 as in the OEIS, are the positive integers whose iterated decimal digit
sum (the single digit eventually reached by repeatedly summing the digits) is a power of 2:
1, 2, 4, 8, 10, 11, 13, 17, 19, 20, ... Iterating the digit sum n times from n always reaches
that single digit, since every step strictly decreases a number with at least two digits and
fixes a single digit. The entry records Colin Barker's conjectures (Feb 10 2020):
G.f. x (1 + x + 2x^2 + 4x^3 + x^4) / ((1 - x)^2 (1 + x) (1 + x^2)) and
a(n) = a(n-1) + a(n-4) - a(n-5) for n > 5. The generating function is stated with its
denominator cleared, using a(0) = 0 as its constant term.
-/

namespace OMA.S_oeis_a028836

open PowerSeries

/-- The sum of the decimal digits of `m`. -/
def digitSum (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- The iterated digit sum of `n`: the digit sum applied `n` times. -/
def iteratedDigitSum (n : ℕ) : ℕ := digitSum^[n] n

/-- Membership in A028836. -/
def IsTerm (n : ℕ) : Prop := 0 < n ∧ ∃ k : ℕ, iteratedDigitSum n = 2 ^ k

/-- The n-th term for n ≥ 1 (offset 1), with `a 0 = 0`. -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else Nat.nth IsTerm (n - 1)

theorem main :
    (mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) =
      X * (1 + X + 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5)) := by
  sorry

end OMA.S_oeis_a028836
