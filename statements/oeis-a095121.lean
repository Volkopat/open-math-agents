import Mathlib

/-!
# A095121: the least m > 0 with 2-adic valuation n of the Catalan number C(m)

Source: https://oeis.org/A095121
Credit: @ivillar

A095121 (offset 0): expansion of (1-x+2x^2)/((1-x)*(1-2x)); data 1, 2, 6, 14, 30, 62, 126, ...
Conjecture (L. Edson Jeffery): a(n) is the least m > 0 such that A007814(A000108(m)) = n,
where A000108 gives the Catalan numbers and A007814(x) is the 2-adic valuation of x.

Formalization notes.
* The denominator (1-x)*(1-2x) has constant coefficient 1, so it is a unit of ℤ⟦X⟧ and is
  inverted with PowerSeries.invOfUnit; a(n) is the coefficient of x^n of the quotient.
* A000108(m) is Mathlib's catalan m, and A007814 is padicValNat 2.
* The statement says: for every n, a(n) is a natural number m which is the least element of the
  set of k > 0 with padicValNat 2 (catalan k) = n.
-/

namespace OMA.S_oeis_a095121

open PowerSeries

/-- A095121: the coefficients of (1 - x + 2x^2)/((1 - x)(1 - 2x)). -/
noncomputable def a (n : ℕ) : ℤ :=
  coeff n ((1 - X + 2 * X ^ 2) * invOfUnit ((1 - X) * (1 - 2 * X)) 1 : PowerSeries ℤ)

/-- Jeffery's conjecture: a(n) is the least m > 0 such that the 2-adic valuation of the Catalan
number C(m) is n. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ, (m : ℤ) = a n ∧
    IsLeast {k : ℕ | 0 < k ∧ padicValNat 2 (catalan k) = n} m := by
  sorry

end OMA.S_oeis_a095121
