import Mathlib

/-!
# OEIS A005379: Plouffe's conjectured generating function of the Hofstadter male sequence

Source: https://oeis.org/A005379, offset 0. The entry records Simon Plouffe's
1992 conjecture and Sahand Saba's counterexample at coefficient 33.

The sequence starts from `M(0) = 0` and `F(0) = 1`, then uses
`M(n) = n − F(M(n−1))` and `F(n) = n − M(F(n−1))` for `n > 0`.
We store the two initial segments in a pair of lists. The new male term is
appended before computing the new female term, which can consult it at `n = 1`.
At each positive index both outputs are bounded by their index, so all
indices used in the recursion are present in the corresponding lists.

The rational series is stated after multiplication by its denominator.
The factors `(X + 1)(X² + 1)(X⁴ + 1)(X − 1)²` of that denominator multiply
to `(1 − X⁸)(1 − X)`, whose constant term is 1.
-/

namespace OMA.S_oeis_a005379

/-- The male and female lists, both up to and including index `n`. -/
def histories : ℕ → List ℕ × List ℕ
  | 0 => ([0], [1])
  | n + 1 =>
    let old := histories n
    let m := n + 1 - old.2[old.1[n]!]!
    let male := old.1 ++ [m]
    let f := n + 1 - male[old.2[n]!]!
    (male, old.2 ++ [f])

/-- The male term `M(n)`, indexed from zero. -/
def a (n : ℕ) : ℕ := (histories n).1[n]!

open PowerSeries

/-- The generating function of the male terms. -/
noncomputable def gf : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))

/-- Plouffe's conjectured generating function, after clearing the denominator. -/
theorem main :
    gf * ((1 - X ^ 8) * (1 - X)) =
      X ^ 2 * (1 + X ^ 3 + X ^ 6 + X + X ^ 4 + X ^ 7 - X ^ 8) := by
  sorry

end OMA.S_oeis_a005379
