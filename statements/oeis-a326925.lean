import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Irreducibility of the derivative numerators in A326925

Source: https://oeis.org/A326925
Credit: @blakestone-x

The derivative order is zero for the first displayed polynomial, which has degree one.
The numerator is taken in reduced form. Nonzero rational normalizations preserve irreducibility.
-/

namespace OMA.S_oeis_a326925

open Polynomial

noncomputable def derivative (r : RatFunc ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (r.num.derivative * r.denom - r.num * r.denom.derivative) /
    (algebraMap ℚ[X] (RatFunc ℚ) r.denom)^2

noncomputable def f : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (1-X) / algebraMap ℚ[X] (RatFunc ℚ) (1-X-X^2)

noncomputable def row (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ)⁻¹) * (derivative^[n] f).num

theorem main : 
    (∀ n : ℕ, Odd (row n).natDegree → Irreducible (row n)) ∧
    (∀ n k : ℕ, 0 < k → (row n).natDegree = 2*k →
      ∃ p q : ℚ[X], row n = p*q ∧ Irreducible p ∧ Irreducible q ∧
        p.natDegree = k ∧ q.natDegree = k) := by
  sorry

end OMA.S_oeis_a326925
