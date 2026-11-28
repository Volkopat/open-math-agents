import Mathlib

/-!
# A183247: Number of permutations of 1..2*n+4 with each element displaced by at least n.

Source: https://oeis.org/A183247
Credit: @bmendonca3

[Full Lean proof by @jiyongparkphysics](https://github.com/jiyongparkphysics/open-math-agents/blob/46ae96cadf00e887a5efafe674e510df2486a43d/proofs/oeis-a183247.lean)

[Independent Lean proofs of a(2) = 1708 and a(3) = 13365](https://github.com/bmendonca3/open-math-agents/blob/2f6956a9b734510c92ed8899086f3ba37e088c72/research/displaced-permutations/FiniteValues.lean)

Entry A183247 (R. H. Hardin, Jan 03 2011), offset 1, data 265, 1708, 13365, 114124, 998112,
8751552, ...
Formula section:
Conjectures from Colin Barker, Mar 27 2018:
G.f.: x*(265 - 4122*x + 17394*x^2 - 7150*x^3 - 29191*x^4 - 100844*x^5) / ((1 - 5*x)*(1 - 8*x)*(1 - 9*x)).
a(n) = 22*a(n-1) - 157*a(n-2) + 360*a(n-3) for n>6.

`main` is the conjunction of the two conjectures.

Formalization notes:
* A permutation of 1..2*n+4 is a permutation p of `Fin (2 * n + 4)`, whose elements are
  0..2*n+3. The shift by one changes no difference p(i) - i, so the count is the same.
* Each element displaced by at least n: |p(i) - i| >= n for every i. The data settle the reading:
  for n = 1 the count is 265, the number of derangements of 6 elements, and the entry gives
  examples of permutations of 1-8 with minimum displacement 2 for n = 2. The sequence is defined
  from this count, not from any of the conjectured formulas.
* G.f.: the offset is 1, so A(x) = Sum_{n >= 1} a(n) x^n has constant term 0. The Lean function
  `a` also has a value at 0, which is not a term of the sequence, so the coefficient of x^0 is set
  to 0. The quotient is stated as the identity
  A(x) * ((1 - 5x)(1 - 8x)(1 - 9x)) =
  x(265 - 4122x + 17394x^2 - 7150x^3 - 29191x^4 - 100844x^5) in the formal power series ring
  over the rationals. This is the same claim, because the denominator has constant term 1 and is
  invertible.
* Recurrence: stated for every n > 6, as the source writes it. Then n - 1, n - 2 and n - 3 are at
  least 4, so only terms of the sequence occur. It is stated in the integers, so the subtraction
  is the true subtraction.
* The entry also has the line: Empirical (for n>=4): 85264*9^(n-4) + 7203*2^(3*n-10) +
  48*5^(n-4). - Vaclav Kotesovec, Nov 27 2012. That line is not one of the conjectures of Barker
  and is not a part of `main`.
-/

namespace OMA.S_oeis_a183247

open PowerSeries

/-- A183247: the number of permutations `p` of `2 * n + 4` elements with each element displaced by
at least `n`, that is `|p(i) - i| ≥ n` for every `i`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin (2 * n + 4)))).filter
    (fun p => ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 5 * X) * (1 - 8 * X) * (1 - 9 * X)) =
      X * (265 - 4122 * X + 17394 * X ^ 2 - 7150 * X ^ 3 - 29191 * X ^ 4 - 100844 * X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 22 * a (n - 1) - 157 * a (n - 2) + 360 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a183247
