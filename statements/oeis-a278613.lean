import Mathlib

/-!
# A278613: Sum of terms in level n of TRIP -  Stern sequence associated with permutation triple (e,e,132).

Source: https://oeis.org/A278613
Credit: @agchua

R. J. Mathar (Dec 02 2016), in the formula section of A278613:
  Conjecture: G.f.: ( -3-5*x-7*x^2 ) / ( -1+x+2*x^2+6*x^3 ).
Stated as an identity of formal power series over ℚ (offset 0):
(∑ a(n) X^n) * (-1 + X + 2X^2 + 6X^3) = -3 - 5X - 7X^2.
Definition (I. Amburg et al., arXiv:1509.05239, the reference of the entry): the TRIP-Stern
sequence of a permutation triple is the sequence of triples T(1) = (1, 1, 1), T(2m) = F0(T(m)), T(2m+1) = F1(T(m)) for m ≥ 1, and level n
consists of the T(l) with 2^n ≤ l < 2^(n+1); a(n) is the sum of the three entries of all T(l) in
level n. For the triple (e, e, 132) the maps are F0(x, y, z) = (y, z, x + z) and
F1(x, y, z) = (y, x + z, x). This is the convention of R. J. Mathar's Maple programs in the sibling
entries A271485 - A271489 and A278614 - A278616: there the maps for the identity are
F0(x, y, z) = (y, z, x + z), F1(x, y, z) = (x, y, x + z), and a permutation in the second or third
place permutes the three output places (for 132: (u, v, w) becomes (v, w, u)). With these maps the
definition below gives all 20 listed terms of A278613 (and for (e, e, e) the g.f. of A278612).
-/

namespace OMA.S_oeis_a278613

/-- The map F0 of the permutation triple (e, e, 132): (x, y, z) ↦ (y, z, x + z). -/
def F0 (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (v.2.1, v.2.2, v.1 + v.2.2)

/-- The map F1 of the permutation triple (e, e, 132): (x, y, z) ↦ (y, x + z, x). -/
def F1 (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (v.2.1, v.1 + v.2.2, v.1)

/-- The TRIP-Stern sequence: T(1) = (1, 1, 1), T(2m) = F0(T(m)), T(2m+1) = F1(T(m)) (the value at 0
is not used). -/
def T (n : ℕ) : ℕ × ℕ × ℕ :=
  if _h : n ≤ 1 then (1, 1, 1)
  else if n % 2 = 0 then F0 (T (n / 2)) else F1 (T (n / 2))
decreasing_by all_goals omega

/-- A278613: the sum of the entries of the triples T(l), 2^n ≤ l < 2^(n+1). -/
def a (n : ℕ) : ℕ := ∑ l ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), ((T l).1 + (T l).2.1 + (T l).2.2)

/-- Mathar's conjecture: the g.f. is (-3-5x-7x^2)/(-1+x+2x^2+6x^3). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
    (-1 + PowerSeries.X + 2 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3) =
      -3 - 5 * PowerSeries.X - 7 * PowerSeries.X ^ 2 := by
  sorry

end OMA.S_oeis_a278613
