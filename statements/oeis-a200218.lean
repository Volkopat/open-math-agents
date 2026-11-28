import Mathlib

/-!
# A200218: The differences x^3 - y^2 of Danilov's subsequence of good Hall's examples A078933.

Source: https://oeis.org/A200218
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A200218 (R. J. Mathar, Nov 15 2011):
a(n) = -1860497*a(n-1) + 1860497*a(n-2) + a(n-3).

Conventions:
* The sequence has offset 1 (data -297, 548147655, -1019827620252441, ...).
* Danilov's sequence is the explicit family produced by the generator of the entry (its first
  Mathematica program): with uu = 682 + 61*sqrt(125) and vv = uu^(2n-1), put
  tt = ((-1)^n*vv[[1]] + 57)/125, where vv[[1]] is the rational part of vv,
  xx = 5^5*tt^2 - 3000*tt + 719 (this is A200216(n)), yy = Round[Sqrt[xx^3]] (this is A200217(n))
  and dd = xx^3 - yy^2 (this is A200218(n)).
* `pw k` below is the pair (E, F) of integers with uu^k = E + F*sqrt(125); it is computed by
  (E + F*sqrt(125))*(682 + 61*sqrt(125)) = (682*E + 125*61*F) + (61*E + 682*F)*sqrt(125).
* tt and xx are formed in `ℚ` so that the division by 125 is exact (xx is an integer). The square
  root is the real square root `Real.sqrt` and Round is `round`, the nearest integer.
* a(n) = dd = xx^3 - yy^2 is formed in `ℚ` (it is an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 4`, which is
  exactly the range in which all the indices n-1, n-2, n-3 are at least the offset 1.
* Mathar's generating function 297*z*(1 + 14882*z + z^2) / ((z-1)*(z^2 + 1860498*z + 1)) is not
  stated separately: given the first three terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a200218

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

/-- A200218 (offset 1): a(n) = xx^3 - yy^2. -/
noncomputable def a (n : ℕ) : ℚ := x n ^ 3 - (y n : ℚ) ^ 2

/-- For every `n ≥ 4`, a(n) = -1860497*a(n-1) + 1860497*a(n-2) + a(n-3). -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n = -1860497 * a (n - 1) + 1860497 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a200218
