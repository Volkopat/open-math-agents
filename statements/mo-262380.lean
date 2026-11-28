import Mathlib

/-!
# Distinct complex roots of a polynomial linked to mock theta functions

T. Amdeberhan asks whether every polynomial in the family below has
distinct complex roots for indices at least two. The product for `n = 0`
is empty and contributes the constant term one.

Source: https://mathoverflow.net/questions/262380
Lean statement by @jacklarmer.
-/

namespace OMA.S_mo_262380

open scoped BigOperators

theorem main :
    ∀ k : ℕ, 2 ≤ k →
      let X : Polynomial ℂ := Polynomial.X
      let Q : Polynomial ℂ :=
        ∑ n ∈ Finset.range k, ∏ j ∈ Finset.Icc 1 n, X * (1 + X ^ j) ^ 2
      Q.roots.Nodup := by
  sorry

end OMA.S_mo_262380
