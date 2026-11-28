import Mathlib

/-!
# A278616: Sum of terms in level n of TRIP -  Stern sequence associated with permutation triple (e,13,132).

Source: https://oeis.org/A278616
Credit: @agchua

R. J. Mathar (Dec 02 2016), in the formula section of A278616:
  Conjecture: G.f.: ( -3-5*x-x^2 ) / ( -1+x+4*x^2+x^3 ).
Stated as an identity of formal power series over ℚ (offset 0):
(∑ a(n) X^n) * (-1 + X + 4X^2 + X^3) = -3 - 5X - X^2.
Definition, as in the entry's programs (TRIP-Stern sequences of I. Amburg et al., arXiv:1509.05239):
the sequence of triples T(1) = (1, 1, 1), T(2m) = F0(T(m)), T(2m+1) = F1(T(m)) for m ≥ 1, with
F0(x, y, z) = (x + z, z, y) and F1(x, y, z) = (y, x + z, x); level n consists of the T(l) with
2^n ≤ l < 2^(n+1), and a(n) is the sum of the three entries of all T(l) in level n, as in the name
and in the Mathematica program, which adds L[[1]] + L[[2]] + L[[3]]. (The active line of the Maple
program adds only L[2]; that gives 1 at n = 0, not the listed 3.) This gives all 20 listed terms.
-/

namespace OMA.S_oeis_a278616

/-- The map F0 of the permutation triple (e, 13, 132): (x, y, z) ↦ (x + z, z, y). -/
def F0 (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (v.1 + v.2.2, v.2.2, v.2.1)

/-- The map F1 of the permutation triple (e, 13, 132): (x, y, z) ↦ (y, x + z, x). -/
def F1 (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (v.2.1, v.1 + v.2.2, v.1)

/-- The TRIP-Stern sequence: T(1) = (1, 1, 1), T(2m) = F0(T(m)), T(2m+1) = F1(T(m)) (the value at 0
is not used). -/
def T (n : ℕ) : ℕ × ℕ × ℕ :=
  if _h : n ≤ 1 then (1, 1, 1)
  else if n % 2 = 0 then F0 (T (n / 2)) else F1 (T (n / 2))
decreasing_by all_goals omega

/-- A278616: the sum of the entries of the triples T(l), 2^n ≤ l < 2^(n+1). -/
def a (n : ℕ) : ℕ := ∑ l ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), ((T l).1 + (T l).2.1 + (T l).2.2)

/-- Mathar's conjecture: the g.f. is (-3-5x-x^2)/(-1+x+4x^2+x^3). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
    (-1 + PowerSeries.X + 4 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) =
      -3 - 5 * PowerSeries.X - PowerSeries.X ^ 2 := by
  sorry

end OMA.S_oeis_a278616
