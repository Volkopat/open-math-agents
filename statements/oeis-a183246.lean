import Mathlib

/-!
# A183246: Number of permutations of 1..2*n+3 with each element displaced by at least n.

Source: https://oeis.org/A183246
Credit: @bmendonca3

[Full Lean proof by @jiyongparkphysics](https://github.com/jiyongparkphysics/open-math-agents/blob/1b3d3fddf7c7a3c9c5eb87187189ead490736001/proofs/oeis-a183246.lean)

[Independent Lean proofs of a(2) = 206](https://github.com/bmendonca3/open-math-agents/blob/2f6956a9b734510c92ed8899086f3ba37e088c72/research/displaced-permutations/FiniteValues.lean)

Entry A183246 (R. H. Hardin, Jan 03 2011), offset 1, data 44, 206, 1168, 6984, 41808, 250464, ...
Formula section:
Conjectures from Colin Barker, Mar 27 2018:
G.f.: 2*x*(22 - 117*x + 82*x^2 + 124*x^3) / ((1 - 4*x)*(1 - 6*x)).
a(n) = 10*a(n-1) - 24*a(n-2) for n>4.

`main` is the conjunction of the two conjectures.

Formalization notes:
* A permutation of 1..2*n+3 is a permutation p of `Fin (2 * n + 3)`, whose elements are
  0..2*n+2. The shift by one changes no difference p(i) - i, so the count is the same.
* Each element displaced by at least n: |p(i) - i| >= n for every i. The data settle the reading:
  for n = 1 the count is 44, the number of derangements of 5 elements, and the entry gives
  examples of permutations of 1-7 with minimum displacement 2 for n = 2. The sequence is defined
  from this count, not from any of the conjectured formulas.
* G.f.: the offset is 1, so A(x) = Sum_{n >= 1} a(n) x^n has constant term 0. The Lean function
  `a` also has a value at 0, which is not a term of the sequence, so the coefficient of x^0 is set
  to 0. The quotient is stated as the identity
  A(x) * ((1 - 4x)(1 - 6x)) = 2x(22 - 117x + 82x^2 + 124x^3) in the formal power series ring over
  the rationals. This is the same claim, because the denominator has constant term 1 and is
  invertible.
* Recurrence: stated for every n > 4, as the source writes it. Then n - 1 and n - 2 are at least
  3, so only terms of the sequence occur. It is stated in the integers, so the subtraction is the
  true subtraction.
* The entry also has the line: Empirical (for n>=3): 289/9*6^(n-1) + 3*4^(n-2). - Vaclav
  Kotesovec, Nov 27 2012. That line is not one of the conjectures of Barker and is not a part of
  `main`.
-/

namespace OMA.S_oeis_a183246

open PowerSeries

/-- A183246: the number of permutations `p` of `2 * n + 3` elements with each element displaced by
at least `n`, that is `|p(i) - i| ≥ n` for every `i`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin (2 * n + 3)))).filter
    (fun p => ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 4. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 4 * X) * (1 - 6 * X)) =
      2 * X * (22 - 117 * X + 82 * X ^ 2 + 124 * X ^ 3) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 10 * a (n - 1) - 24 * a (n - 2)) := by
  sorry

end OMA.S_oeis_a183246
