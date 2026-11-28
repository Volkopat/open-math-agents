import Mathlib

/-!
# A200217: Danilov's sequence of y values satisfying 0 < |x^3 - y^2| < sqrt(x) with integer (x,y).

Source: https://oeis.org/A200217
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A200217 (R. J. Mathar, Nov 15 2011):
a(n) = +6440022564929296994*a(n-1) +22291834190970757443015664937985*a(n-2)
-41473935220466903245533179036528718020*a(n-3) +22291834190970757443015664937985*a(n-4)
+6440022564929296994*a(n-5) -a(n-6).

Conventions:
* The sequence has offset 1 (data 28748141, 182720147509505842286585077, ...).
* Danilov's sequence is the explicit family produced by the generator of the entry (its first
  Mathematica program): with uu = 682 + 61*sqrt(125) and vv = uu^(2n-1), put
  tt = ((-1)^n*vv[[1]] + 57)/125, where vv[[1]] is the rational part of vv,
  xx = 5^5*tt^2 - 3000*tt + 719 (this is A200216(n)), yy = Round[Sqrt[xx^3]] (this is A200217(n))
  and dd = xx^3 - yy^2 (this is A200218(n)).
* `pw k` below is the pair (E, F) of integers with uu^k = E + F*sqrt(125); it is computed by
  (E + F*sqrt(125))*(682 + 61*sqrt(125)) = (682*E + 125*61*F) + (61*E + 682*F)*sqrt(125).
* tt and xx are formed in `ℚ` so that the division by 125 is exact (xx is an integer). The square
  root is the real square root `Real.sqrt` and Round is `round`, the nearest integer.
* The source gives no range for n. The recurrence is asserted for every `n ≥ 7`, which is
  exactly the range in which all the indices n-1, ..., n-6 are at least the offset 1.
* Mathar's equivalent generating function is not stated separately: given the first six terms it
  is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a200217

/-- `(682 + 61*sqrt(125))^k = E + F*sqrt(125)`: the pair `(E, F)`. -/
def pw : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => (682 * (pw k).1 + 125 * 61 * (pw k).2, 61 * (pw k).1 + 682 * (pw k).2)

/-- tt = ((-1)^n*vv[[1]] + 57)/125, where vv = (682 + 61*sqrt(125))^(2n-1). -/
def t (n : ℕ) : ℚ := ((-1) ^ n * ((pw (2 * n - 1)).1 : ℚ) + 57) / 125

/-- xx = 5^5*tt^2 - 3000*tt + 719, the n-th term of A200216. -/
def x (n : ℕ) : ℚ := 5 ^ 5 * t n ^ 2 - 3000 * t n + 719

/-- yy = Round[Sqrt[xx^3]], the n-th term of A200217. -/
noncomputable def y (n : ℕ) : ℤ := round (Real.sqrt ((x n : ℝ) ^ 3))

/-- A200217 (offset 1). -/
noncomputable def a (n : ℕ) : ℤ := y n

/-- For every `n ≥ 7`, a(n) = 6440022564929296994*a(n-1)
+ 22291834190970757443015664937985*a(n-2) - 41473935220466903245533179036528718020*a(n-3)
+ 22291834190970757443015664937985*a(n-4) + 6440022564929296994*a(n-5) - a(n-6). -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    a n = 6440022564929296994 * a (n - 1) + 22291834190970757443015664937985 * a (n - 2)
      - 41473935220466903245533179036528718020 * a (n - 3)
      + 22291834190970757443015664937985 * a (n - 4)
      + 6440022564929296994 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a200217
