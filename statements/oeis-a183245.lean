import Mathlib

/-!
# A183245: Number of permutations of 1..2*n+2 with each element displaced by at least n.

Source: https://oeis.org/A183245
Credit: @bmendonca3

[Lean proof by middle-row enumeration](https://github.com/bmendonca3/open-math-agents/blob/1dbd829dcf36e156a64967cf1b77ad6876febea0/proofs/oeis-a183245.lean)

[Separate Lean proof by @jiyongparkphysics](https://github.com/jiyongparkphysics/open-math-agents/blob/3f5938a5090fb58e0aa2537a7cff075466908ab7/proofs/oeis-a183245.lean)

Entry A183245 (R. H. Hardin, Jan 03 2011), offset 1, data 9, 29, 112, 436, 1708, 6724, 26572, ...
Formula section:
Conjectures from Colin Barker, Mar 27 2018:
G.f.: x*(9 - 34*x + 17*x^2) / ((1 - 3*x)*(1 - 4*x)).
a(n) = 7*a(n-1) - 12*a(n-2) for n>3.

`main` is the conjunction of the two conjectures.

Formalization notes:
* A permutation of 1..2*n+2 is a permutation p of `Fin (2 * n + 2)`, whose elements are
  0..2*n+1. The shift by one changes no difference p(i) - i, so the count is the same.
* Each element displaced by at least n: |p(i) - i| >= n for every i. The data settle the reading:
  for n = 1 the count is 9, the number of derangements of 4 elements, and for n = 2 the count is
  29, the number of permutations of 1-6 with minimum displacement 2 that the entry lists. The
  sequence is defined from this count, not from any of the conjectured formulas.
* G.f.: the offset is 1, so A(x) = Sum_{n >= 1} a(n) x^n has constant term 0. The Lean function
  `a` also has a value at 0, which is not a term of the sequence, so the coefficient of x^0 is set
  to 0. The quotient is stated as the identity A(x) * ((1 - 3x)(1 - 4x)) = x(9 - 34x + 17x^2) in
  the formal power series ring over the rationals. This is the same claim, because the
  denominator has constant term 1 and is invertible.
* Recurrence: stated for every n > 3, as the source writes it. Then n - 1 and n - 2 are at least
  2, so only terms of the sequence occur. It is stated in the integers, so the subtraction is the
  true subtraction.
* The entry also has the line: Empirical (for n>=2): 25*4^(n-2) + 4*3^(n-2). - Vaclav Kotesovec,
  Nov 27 2012. That line is not one of the conjectures of Barker and is not a part of `main`.
-/

namespace OMA.S_oeis_a183245

open PowerSeries

/-- A183245: the number of permutations `p` of `2 * n + 2` elements with each element displaced by
at least `n`, that is `|p(i) - i| ≥ n` for every `i`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin (2 * n + 2)))).filter
    (fun p => ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 3. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 3 * X) * (1 - 4 * X)) =
      X * (9 - 34 * X + 17 * X ^ 2) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 7 * a (n - 1) - 12 * a (n - 2)) := by
  sorry

end OMA.S_oeis_a183245
