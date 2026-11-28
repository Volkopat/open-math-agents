import Mathlib

/-!
# A278614: Sum of terms in level n of TRIP -  Stern sequence associated with permutation triple (e,12,12).

Source: https://oeis.org/A278614
Credit: @agchua

R. J. Mathar (Dec 02 2016), in the formula section of A278614:
  Conjecture: G.f.: ( 3-x-5*x^2 ) / ( 1-3*x-x^2+4*x^3 ).
Stated as an identity of formal power series over ℚ (offset 0):
(∑ a(n) X^n) * (1 - 3X - X^2 + 4X^3) = 3 - X - 5X^2.
Definition, as in R. J. Mathar's Maple program in the entry (TRIP-Stern sequences of I. Amburg et al.,
arXiv:1509.05239): the sequence of triples T(1) = (1, 1, 1), T(2m) = F0(T(m)), T(2m+1) = F1(T(m))
for m ≥ 1, with F0(x, y, z) = (z, y, x + z) and F1(x, y, z) = (y, x, x + z); level n consists of the
T(l) with 2^n ≤ l < 2^(n+1), and a(n) is the sum of the three entries of all T(l) in level n (the
program adds L[1] + L[2] + L[3] for l from 2^n to 2^(n+1) - 1). This gives all 20 listed terms.
-/

namespace OMA.S_oeis_a278614

/-- The map F0 of the permutation triple (e, 12, 12): (x, y, z) ↦ (z, y, x + z). -/
def F0 (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (v.2.2, v.2.1, v.1 + v.2.2)

/-- The map F1 of the permutation triple (e, 12, 12): (x, y, z) ↦ (y, x, x + z). -/
def F1 (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (v.2.1, v.1, v.1 + v.2.2)

/-- The TRIP-Stern sequence: T(1) = (1, 1, 1), T(2m) = F0(T(m)), T(2m+1) = F1(T(m)) (the value at 0
is not used). -/
def T (n : ℕ) : ℕ × ℕ × ℕ :=
  if _h : n ≤ 1 then (1, 1, 1)
  else if n % 2 = 0 then F0 (T (n / 2)) else F1 (T (n / 2))
decreasing_by all_goals omega

/-- A278614: the sum of the entries of the triples T(l), 2^n ≤ l < 2^(n+1). -/
def a (n : ℕ) : ℕ := ∑ l ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), ((T l).1 + (T l).2.1 + (T l).2.2)

/-- Mathar's conjecture: the g.f. is (3-x-5x^2)/(1-3x-x^2+4x^3). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
    (1 - 3 * PowerSeries.X - PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3) =
      3 - PowerSeries.X - 5 * PowerSeries.X ^ 2 := by
  sorry

end OMA.S_oeis_a278614
