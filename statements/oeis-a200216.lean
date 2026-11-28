import Mathlib

/-!
# A200216: Danilov's sequence of x satisfying 0 < |x^3-y^2| < sqrt(x) with integer (x,y).

Source: https://oeis.org/A200216
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A200216 (R. J. Mathar, Nov 15 2011):
a(n) = 3461450947505*a(n-1) + 6440022564931157490*a(n-2) - 6440022564931157490*a(n-3)
- 3461450947505*a(n-4) + a(n-5).

Conventions:
* The sequence has offset 1 (data 93844, 322001299796379844, ...).
* Danilov's sequence is the explicit family produced by the generator of the entry (the
  Mathematica program and the PARI program by Noam D. Elkies): with uu = 682 + 61*sqrt(125)
  (= quadunit(20)^5) and vv = uu^(2n-1), put tt = ((-1)^n*vv[[1]] + 57)/125, where vv[[1]] is the
  rational part of vv, and a(n) = 5^5*tt^2 - 3000*tt + 719.
* `pw k` below is the pair (E, F) of integers with uu^k = E + F*sqrt(125); it is computed by
  (E + F*sqrt(125))*(682 + 61*sqrt(125)) = (682*E + 125*61*F) + (61*E + 682*F)*sqrt(125).
* tt and a(n) are formed in `ℚ` so that the division by 125 is exact (a(n) is an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 6`, which is
  exactly the range in which all the indices n-1, ..., n-5 are at least the offset 1.
* Mathar's generating function is not stated separately: given the first five terms it is the
  same assertion as the recurrence.
-/

namespace OMA.S_oeis_a200216

/-- `(682 + 61*sqrt(125))^k = E + F*sqrt(125)`: the pair `(E, F)`. -/
def pw : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => (682 * (pw k).1 + 125 * 61 * (pw k).2, 61 * (pw k).1 + 682 * (pw k).2)

/-- tt = ((-1)^n*vv[[1]] + 57)/125, where vv = (682 + 61*sqrt(125))^(2n-1). -/
def t (n : ℕ) : ℚ := ((-1) ^ n * ((pw (2 * n - 1)).1 : ℚ) + 57) / 125

/-- A200216 (offset 1): a(n) = 5^5*tt^2 - 3000*tt + 719. -/
def a (n : ℕ) : ℚ := 5 ^ 5 * t n ^ 2 - 3000 * t n + 719

/-- For every `n ≥ 6`, a(n) = 3461450947505*a(n-1) + 6440022564931157490*a(n-2)
- 6440022564931157490*a(n-3) - 3461450947505*a(n-4) + a(n-5). -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    a n = 3461450947505 * a (n - 1) + 6440022564931157490 * a (n - 2)
      - 6440022564931157490 * a (n - 3) - 3461450947505 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a200216
