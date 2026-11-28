import Mathlib

/-!
# A199899: Number of -n..n arrays x(0..3) of 4 elements with zero sum, and adjacent elements not both strictly positive and not both strictly negative.

Source: https://oeis.org/A199899
Credit: @Salofe

Conjectures from Colin Barker, Feb 23 2018, quoted verbatim from the entry:
* "G.f.: x*(3 - x)*(5 - 2*x + x^2) / (1 - x)^4."
* "a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4."

Formalization notes:
* Offset 1, as in the entry (data: 15, 49, 111, 209, 351, 545, ...).
* An array x(0..3) is a 4-tuple `(x0, x1, x2, x3) : ℤ × ℤ × ℤ × ℤ`, each entry in `-n..n`
  (`Finset.Icc (-n) n`); "zero sum" is `x0 + x1 + x2 + x3 = 0`.
* The adjacent elements of the array are the three pairs `(x0, x1)`, `(x1, x2)`, `(x2, x3)`
  (a linear array, no wrap-around from `x3` to `x0`). For each such pair `(u, v)` the condition
  is written out literally: `¬ (0 < u ∧ 0 < v) ∧ ¬ (u < 0 ∧ v < 0)`. This reading reproduces the
  data: a brute-force evaluation of this definition gives a(1..4) = 15, 49, 111, 209 and agrees
  with the entry's b-file for n = 1..15, while the wrap-around reading would give a(2) = 45.
  It is also consistent with the entry's example array (-3, 6, 0, -3) for n = 6, whose first and
  last elements are both strictly negative.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` in the form N * D⁻¹ with N = x(3 - x)(5 - 2x + x^2) and D = (1 - x)^4 (D has
  constant coefficient 1, so it is invertible). The definition also makes sense for n = 0 (where
  it counts the zero array), outside the range of the entry, so the coefficient of x^0 of the
  series is set to 0.
* The recurrence is stated in `ℤ` for every n > 4, as in the entry (all indices are then >= 1).
-/

namespace OMA.S_oeis_a199899

/-- A199899(n): the number of arrays `(x0, x1, x2, x3)` with every entry in `-n..n`, zero sum,
and no two adjacent elements both strictly positive or both strictly negative. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ
      Finset.Icc (-(n : ℤ)) n).filter
    (fun ⟨x0, x1, x2, x3⟩ =>
      x0 + x1 + x2 + x3 = 0 ∧
      ¬ (0 < x0 ∧ 0 < x1) ∧ ¬ (x0 < 0 ∧ x1 < 0) ∧
      ¬ (0 < x1 ∧ 0 < x2) ∧ ¬ (x1 < 0 ∧ x2 < 0) ∧
      ¬ (0 < x2 ∧ 0 < x3) ∧ ¬ (x2 < 0 ∧ x3 < 0))).card

open PowerSeries in
/-- Barker's conjectures: the generating function `x(3 - x)(5 - 2x + x^2)/(1 - x)^4`, and the
recurrence `a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 4`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
        (X * (3 - X) * (5 - 2 * X + X ^ 2)) * ((1 - X) ^ 4)⁻¹ ∧
    ∀ n : ℕ, 4 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a199899
