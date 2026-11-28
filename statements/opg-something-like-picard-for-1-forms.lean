import Mathlib

/-!
# Something like Picard for 1-forms

Source: https://www.openproblemgarden.org/op/something_like_picard_for_1_forms
Credit: @lzvxck

The source: let `D` be the open unit disk in the complex plane and let `U₁, ..., U_n` be open
sets such that `⋃ U_j = D \ {0}`. Suppose there are injective holomorphic functions
`f_j : U_j → ℂ` such that for the differentials `d f_j = d f_k` on any intersection
`U_j ∩ U_k`. Then those differentials glue together to a meromorphic 1-form on `D`.

Conventions: the functions are `f j : ℂ → ℂ`, holomorphic (complex differentiable) and
injective on `U j`; their values off `U j` play no role. On the open set `U j` the differential
is `d f_j = f_j' dz`, so `d f_j = d f_k` on `U_j ∩ U_k` means `f_j' = f_k'` there. The glued
1-form is `g dz`, where `g = f_j'` on each `U_j`; it is holomorphic on `D \ {0}`, and it is
meromorphic on `D` exactly when `g` is meromorphic at `0` (Mathlib's `MeromorphicAt`, which
does not depend on the value `g 0`).
-/

namespace OMA.S_opg_something_like_picard_for_1_forms

/-- **Something like Picard for 1-forms (Elsner).** The derivatives of injective holomorphic
functions on an open cover of the punctured unit disk, agreeing on overlaps, glue to a
function that is meromorphic at the origin. -/
theorem main : ∀ (n : ℕ) (U : Fin n → Set ℂ) (f : Fin n → ℂ → ℂ),
    (∀ j, IsOpen (U j)) → (⋃ j, U j) = Metric.ball (0 : ℂ) 1 \ {0} →
    (∀ j, DifferentiableOn ℂ (f j) (U j)) → (∀ j, Set.InjOn (f j) (U j)) →
    (∀ j k, ∀ z ∈ U j ∩ U k, deriv (f j) z = deriv (f k) z) →
      ∃ g : ℂ → ℂ, (∀ j, ∀ z ∈ U j, g z = deriv (f j) z) ∧ MeromorphicAt g 0 := by
  sorry

end OMA.S_opg_something_like_picard_for_1_forms
