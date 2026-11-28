import Mathlib

/-!
# A249984: length 5 0..2n arrays whose adjacent differences have absolute sum 4n

A249984(n) is the number of arrays `x 0, ..., x 4` (length 4+1 = 5) with entries in
0..2*n such that `∑ i < 4, |x i - x (i + 1)| = 4 * n`. A brute-force count of this
reading gives 64, 384, 1242, 3030, 6252, 11524 for n = 1..6, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 10 2018):
  G.f.: 2*x*(32 + 32*x - 19*x^2 + 10*x^3 + x^4) / (1 - x)^5,
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 5.
The g.f. is stated after multiplying both sides by (1 - x)^5. (R. H. Hardin's empirical
polynomial follows from the g.f.)

Source: https://oeis.org/A249984
Credit: @VashaTS
-/

namespace OMA.S_oeis_a249984

open PowerSeries

/-- The sum of the absolute values of the adjacent differences. -/
def variation {n : ℕ} (x : Fin 5 → Fin (2 * n + 1)) : ℤ :=
  ∑ i : Fin 4, |((x i.castSucc).val : ℤ) - (x i.succ).val|

/-- A249984(n). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 5 → Fin (2 * n + 1) => variation x = 4 * n).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      2 * X * (32 + 32 * X - 19 * X ^ 2 + 10 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a249984
