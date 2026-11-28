import Mathlib

/-!
# A249986: length 7 0..2n arrays whose adjacent differences have absolute sum 6n

A249986(n) is the number of arrays `x 0, ..., x 6` (length 6+1 = 7) with entries in
0..2*n such that `∑ i < 6, |x i - x (i + 1)| = 6 * n`. A brute-force count of this
reading gives 466, 7138, 43068 for n = 1..3, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 10 2018):
  G.f.: 2*x*(233 + 1938*x + 1444*x^2 + 309*x^3 + 134*x^4 - 84*x^5) / (1 - x)^7,
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7)
  for n > 7.
The g.f. is stated after multiplying both sides by (1 - x)^7. (R. H. Hardin's empirical
polynomial follows from the g.f.)

Source: https://oeis.org/A249986
Credit: @VashaTS
-/

namespace OMA.S_oeis_a249986

open PowerSeries

/-- The sum of the absolute values of the adjacent differences. -/
def variation {n : ℕ} (x : Fin 7 → Fin (2 * n + 1)) : ℤ :=
  ∑ i : Fin 6, |((x i.castSucc).val : ℤ) - (x i.succ).val|

/-- A249986(n). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 7 → Fin (2 * n + 1) => variation x = 6 * n).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (233 + 1938 * X + 1444 * X ^ 2 + 309 * X ^ 3 + 134 * X ^ 4 - 84 * X ^ 5) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4)
        + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a249986
