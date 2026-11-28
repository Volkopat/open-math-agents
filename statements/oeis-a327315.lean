import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Irreducibility of the derivative numerators in A327315

Source: https://oeis.org/A327315
Credit: @blakestone-x

The derivative order is zero for the first displayed polynomial, which has degree one.
The numerator is taken in reduced form. Nonzero rational normalizations preserve irreducibility.
-/

namespace OMA.S_oeis_a327315

open Polynomial

noncomputable def derivative (r : RatFunc ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (r.num.derivative * r.denom - r.num * r.denom.derivative) /
    (algebraMap ℚ[X] (RatFunc ℚ) r.denom)^2

noncomputable def f : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (X-2) / algebraMap ℚ[X] (RatFunc ℚ) (X^2-X+1)

noncomputable def row (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ)⁻¹) * (derivative^[n] f).num

theorem main : ∀ n : ℕ, Irreducible (row n) ↔ ∃ a b : ℕ, n+1 = 2^a * 3^b := by
  sorry

end OMA.S_oeis_a327315
