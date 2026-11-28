import Mathlib

/-!
# A262267: Number of (n+2) X (1+2) 0..1 arrays with each row and column divisible by 5, read as a binary number with top and left being the most significant bits.

Source: https://oeis.org/A262267
Credit: @agchua

Colin Barker (Feb 21 2018), in the formula section of A262267:
  Conjectures from Colin Barker, Feb 21 2018: (Start)
  G.f.: x*(2 - 2*x + x^2 - 2*x^3) / ((1 - x)*(1 - 2*x)*(1 + x^2)).
  a(n) = 1/2 + 2^(2+n)/5 - (1/20-i/20)*((1+2*i)*(-i)^n + (2+i)*i^n) where i=sqrt(-1).
  (End)
This file states both parts. The offset is 1, so the g.f. is the series sum over n >= 1 of
a(n) x^n, written as X * mk (fun n => a (n + 1)) and stated as an identity of formal power
series over Q; the closed form is stated in C for n >= 1.
Definition: an array is M : Fin (n + 2) -> Fin 3 -> Fin 2 (row i, column j, entries 0..1).
Row i read as a binary number with the left entry most significant is
4 M(i,0) + 2 M(i,1) + M(i,2); column j read with the top entry most significant is the sum
over i of M(i,j) 2^(n+1-i). a(n) counts the arrays all of whose rows and columns are
divisible by 5. This gives the listed terms 2, 4, 7, 13, 26, 52, 103, ...
-/

namespace OMA.S_oeis_a262267

/-- Row `i` of the array `M`, read as a binary number with the left entry most significant. -/
def rowVal (n : ℕ) (M : Fin (n + 2) → Fin 3 → Fin 2) (i : Fin (n + 2)) : ℕ :=
  4 * (M i 0 : ℕ) + 2 * (M i 1 : ℕ) + (M i 2 : ℕ)

/-- Column `j` of the array `M`, read as a binary number with the top entry most significant. -/
def colVal (n : ℕ) (M : Fin (n + 2) → Fin 3 → Fin 2) (j : Fin 3) : ℕ :=
  ∑ i : Fin (n + 2), (M i j : ℕ) * 2 ^ (n + 1 - (i : ℕ))

/-- A262267(n): the number of (n+2) X 3 arrays with entries 0..1 whose rows and columns, read
as binary numbers, are all divisible by 5. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun M : Fin (n + 2) → Fin 3 → Fin 2 =>
    (∀ i, 5 ∣ rowVal n M i) ∧ (∀ j, 5 ∣ colVal n M j))).card

/-- Barker's conjectures: the g.f. x(2 - 2x + x^2 - 2x^3)/((1 - x)(1 - 2x)(1 + x^2)), and the
closed form a(n) = 1/2 + 2^(2+n)/5 - (1/20 - i/20)((1+2i)(-i)^n + (2+i)i^n) for n >= 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X ^ 2)) =
      PowerSeries.X * (2 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℂ) = 1 / 2 + 2 ^ (2 + n) / 5 -
      (1 / 20 - Complex.I / 20) *
        ((1 + 2 * Complex.I) * (-Complex.I) ^ n + (2 + Complex.I) * Complex.I ^ n) := by
  sorry

end OMA.S_oeis_a262267
