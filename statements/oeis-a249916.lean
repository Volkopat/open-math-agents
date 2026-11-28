import Mathlib

/-!
# A249916: the recurrence, the generating function and the pattern of repeated terms

Source: https://oeis.org/A249916
Credit: @ivillar

A249916 (offset 0): a(n) = 4*(n - 1) - a(n-3) for n ≥ 3, with a(0) = a(1) = 1, a(2) = 5;
data 1, 1, 5, 7, 11, 11, 13, 13, 17, 19, 23, 23, 25, 25, ...

Conjectures recorded in A249916 (all confirmed in the entry by Jianing Song, Jan 28 2019):
* a(n) = 2*a(n-1) - a(n-2) - a(n-3) + 2*a(n-4) - a(n-5) for n > 4;
* the g.f. is (1 - x + 4*x^2 - x^3 + x^4)/((1 - x)^2*(1 + x^3));
* these are the natural numbers of the form 6*j +- 1 in which those of the form 12*k +- 1 are
  repeated.

Formalization: the terms are integers. The g.f. is a formal power series over ℤ, stated with the
denominator cleared. The third clause is stated through the number of indices n with a(n) = m
for each natural number m: it is 2 when m is 1 or 11 modulo 12, it is 1 when m is 5 or 7 modulo
12 (the remaining numbers of the form 6*j +- 1), and 0 otherwise.
-/

namespace OMA.S_oeis_a249916

open PowerSeries

/-- a(0) = a(1) = 1, a(2) = 5, a(n) = 4 (n - 1) - a(n - 3). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 5
  | (n + 3) => 4 * ((n : ℤ) + 2) - a n

/-- The three confirmed conjectures of A249916. -/
theorem main :
    (∀ n : ℕ, 4 < n →
      a n = 2 * a (n - 1) - a (n - 2) - a (n - 3) + 2 * a (n - 4) - a (n - 5)) ∧
    PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X ^ 3)) = 1 - X + 4 * X ^ 2 - X ^ 3 + X ^ 4 ∧
    (∀ m : ℕ, {n : ℕ | a n = (m : ℤ)}.ncard =
      if m % 12 = 1 ∨ m % 12 = 11 then 2 else if m % 12 = 5 ∨ m % 12 = 7 then 1 else 0) := by
  sorry

end OMA.S_oeis_a249916
