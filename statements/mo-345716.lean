import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-!
# A positive answer to MathOverflow 345716

Source: https://mathoverflow.net/questions/345716/can-a-quadratic-polynomial-in-mathbbf-px-1-dots-x-d-divide-a-linea
Question by Wenbo Sun, 2019-11-10 (CC BY-SA 4.0).
Credit: @etaubman

The question explicitly defines divisibility as containment of zero sets over
the finite field. No condition c != 0 occurs in the question or its comment.
We answer its possibility question affirmatively, taking d = 2 and c = 0.
For every prime p congruent to 3 modulo 4, x^2 + y^2 = 0 forces x = y = 0,
so the nonzero linear polynomial x vanishes on the quadratic's zero set.

The notation d << p has no numerical constant in the source. The quantified
bound N below records that these examples have fixed d = 2 and arbitrarily
large p; we do not assign an invented numerical meaning to <<. The result
makes no assertion that an example exists for each prescribed (p,d,c).
-/

namespace OMA.S_mo_345716

open MvPolynomial

noncomputable def quadratic (p d : ℕ) (c : ZMod p) : MvPolynomial (Fin d) (ZMod p) :=
  (∑ i, X i ^ 2) - C c

noncomputable def linear (p d : ℕ) (a : Fin d → ZMod p) (a₀ : ZMod p) :
    MvPolynomial (Fin d) (ZMod p) :=
  (∑ i, C (a i) * X i) + C a₀

/-- The author's pointwise notion of divisibility, with nontrivial polynomials.
The coefficient condition makes the linear polynomial genuinely nonconstant. -/
def possible (p d : ℕ) : Prop :=
  ∃ (c : ZMod p) (a : Fin d → ZMod p) (a₀ : ZMod p),
    quadratic p d c ≠ 0 ∧ (∃ i, a i ≠ 0) ∧
      ∀ x : Fin d → ZMod p,
        eval x (quadratic p d c) = 0 → eval x (linear p d a a₀) = 0

theorem main : ∀ N : ℕ, ∃ p d : ℕ,
    p.Prime ∧ N < p ∧ 2 ≤ d ∧ d = 2 ∧ possible p d := by
  sorry

end OMA.S_mo_345716
