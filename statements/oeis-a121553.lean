import Mathlib

/-!
# A121553: Mathar's recurrence for the total area of deco polyominoes

Source: https://oeis.org/A121553
Credit: @ivillar

A121553 (offset 1): a(n) is the total area of all deco polyominoes of height n;
data 1, 4, 20, 122, 874, 7164, 65988, ... The entry gives the formula
a(1) = 1; a(n) = n*a(n-1) + (n-1)!*[1 + n(n-1)/2] for n ≥ 2 (Barcucci et al., p. 34).

Conjecture (R. J. Mathar, Jul 22 2022): the sequence is D-finite with recurrence
a(n) + (-2*n-3)*a(n-1) + (n^2+4*n-3)*a(n-2) + 2*(-n^2+n+3)*a(n-3) + 2*(n-3)^2*a(n-4) = 0.

Formalization: a(n) is defined by the entry's formula, with n(n-1)/2 written as the binomial
coefficient C(n,2). The value a(0) = 0 is a placeholder outside the OEIS range; the recurrence is
stated for every n ≥ 5, where it involves only a(1), a(2), ...
-/

namespace OMA.S_oeis_a121553

/-- a(1) = 1 and a(n) = n a(n-1) + (n-1)! (1 + C(n,2)) for n ≥ 2; a(0) = 0 is a placeholder. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    ((n : ℤ) + 2) * a (n + 1) + ((n + 1).factorial : ℤ) * (1 + ((n + 2).choose 2 : ℤ))

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + (-2 * (n : ℤ) - 3) * a (n - 1) + ((n : ℤ) ^ 2 + 4 * n - 3) * a (n - 2) +
      2 * (-(n : ℤ) ^ 2 + n + 3) * a (n - 3) + 2 * ((n : ℤ) - 3) ^ 2 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a121553
