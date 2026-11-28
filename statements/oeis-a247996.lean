import Mathlib

/-!
# A247996: length 6 0..n arrays with no two disjoint triples of equal sum

A247996(n) is the number of arrays `x 0, ..., x 5` (length 1+5 = 6) with entries in 0..n
such that no two disjoint triples of terms within six consecutive terms have the same sum.
Since the array has exactly six terms, the six consecutive terms are the whole array and two
disjoint triples are a triple `t` of positions and its complement: the condition is that
`∑ i ∈ t, x i ≠ ∑ i ∉ t, x i` for every set `t` of three positions. A brute-force count of
this reading gives 32, 396, 2292, 9080, 28020, 72972 for n = 1..6, matching the listed
terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 07 2018):
  G.f.: 4*x*(8 + 51*x + 91*x^2 + 106*x^3 + 21*x^4 + 83*x^5) / ((1 - x)^7*(1 + x)),
  a(n) = (2*n^6 + n^5 + 35*n^4 - 5*n^3 + 10*n^2 + 36*n) / 2 for n even,
  a(n) = (2*n^6 + n^5 + 35*n^4 - 5*n^3 + 10*n^2 + 36*n - 15) / 2 for n odd.
The g.f. is stated after multiplying both sides by the denominator; the closed forms are
stated for the terms of the sequence, n ≥ 1.

Source: https://oeis.org/A247996
Credit: @VashaTS
-/

namespace OMA.S_oeis_a247996

open PowerSeries

/-- No triple of positions has the same sum as the complementary triple. -/
def NoEqualTriples (n : ℕ) (x : Fin 6 → Fin (n + 1)) : Prop :=
  ∀ t : Finset (Fin 6), t.card = 3 → ∑ i ∈ t, (x i).val ≠ ∑ i ∈ tᶜ, (x i).val

instance (n : ℕ) (x : Fin 6 → Fin (n + 1)) : Decidable (NoEqualTriples n x) := by
  unfold NoEqualTriples; infer_instance

/-- A247996(n). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 6 → Fin (n + 1) => NoEqualTriples n x).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 7 * (1 + X)) =
      4 * X * (8 + 51 * X + 91 * X ^ 2 + 106 * X ^ 3 + 21 * X ^ 4 + 83 * X ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = (2 * n ^ 6 + n ^ 5 + 35 * n ^ 4 - 5 * n ^ 3 + 10 * n ^ 2 + 36 * n) / 2) ∧
    ∀ n : ℕ, Odd n →
      (a n : ℚ) = (2 * n ^ 6 + n ^ 5 + 35 * n ^ 4 - 5 * n ^ 3 + 10 * n ^ 2 + 36 * n - 15) / 2 := by
  sorry

end OMA.S_oeis_a247996
