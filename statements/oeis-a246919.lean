import Mathlib

/-!
# A246919: longest nontrivial integral cevian of an equilateral triangle of side n

Source: https://oeis.org/A246919 (conjectures by Colin Barker, Jun 06 2016)

Entry (offset 1): The length of the longest nontrivial integral cevian of an equilateral
triangle of side n that divides an edge into two integral parts, or 0 if no such cevian exists.
Comments: a cevian joins a vertex with a point on the opposite side (or its extension); a
nontrivial cevian does not coincide with a side; for an equilateral triangle of side n the
lengths of its cevians are the values of y in the solutions to x^2-y^2-n*x+n^2=0.
Formalization notes:
* Here x is the (signed) distance along the line of the opposite side from one of its endpoints
  to the foot of the cevian, so the two parts of the edge are integral exactly when x is an
  integer; y is the length of the cevian. A cevian coincides with a side exactly when x = 0 or
  x = n, i.e. exactly when y = n, so the nontrivial integral cevians are the natural numbers
  y != n for which some integer x solves the equation, and a(n) is the supremum of this set
  (which is finite); `sSup` of the empty set of natural numbers is 0, matching the entry.
* With this reading the definition reproduces the entry data 0, 0, 7, 0, 19, 14, 37, 13, ...
Formula section, Conjectures from Colin Barker, Jun 06 2016:
a(n) = 3*a(n-4)-3*a(n-8)+a(n-12) for n>14.
G.f.: x^3*(7 +19*x^2 +14*x^3 +16*x^4 +13*x^5 +4*x^6 -4*x^7 +x^8 -11*x^9 +x^10 +2*x^11 +4*x^13) / ((1 -x)^3*(1 +x)^3*(1 +x^2)^3).
* The recurrence is stated with the range n > 14 given in the entry, in the integers.
* With offset 1 the generating function is `A(x) = Sum_(n >= 1) a(n) x^n`; since the denominator
  has constant term 1, `A = N/D` is stated as `A * D = N` in the formal power series ring over
  the integers.
-/

namespace OMA.S_oeis_a246919

open PowerSeries

/-- The lengths of the nontrivial integral cevians of the equilateral triangle of side `n`. -/
def cevians (n : ℕ) : Set ℕ :=
  {y | y ≠ n ∧ ∃ x : ℤ, x ^ 2 - (y : ℤ) ^ 2 - n * x + (n : ℤ) ^ 2 = 0}

/-- A246919(n): the longest nontrivial integral cevian, or 0 if there is none. -/
noncomputable def a (n : ℕ) : ℕ := sSup (cevians n)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 14 < n → (a n : ℤ) = 3 * a (n - 4) - 3 * a (n - 8) + a (n - 12)) ∧
    mk (fun n => if n = 0 then 0 else (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 3) =
      (X ^ 3 * (7 + 19 * X ^ 2 + 14 * X ^ 3 + 16 * X ^ 4 + 13 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 +
        X ^ 8 - 11 * X ^ 9 + X ^ 10 + 2 * X ^ 11 + 4 * X ^ 13) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a246919
