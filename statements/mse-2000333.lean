import Mathlib

/-!
# Field F Isomorphic to F(X, Y) but Not to F(X)

Source: https://math.stackexchange.com/questions/2000333/is-there-a-field-f-which-is-isomorphic-to-fx-y-but-not-to-fx
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Is there a field `F` such that `F ≅ F(X, Y)` as fields, but `F ≇ F(X)` as fields?

## Formalization Notes
`RatFunc F` is the rational function field `F(X)`, and `RatFunc (RatFunc F)` is
`F(X)(Y) ≅ F(X, Y)`. Ring isomorphism `≃+*` between fields is field isomorphism.
-/

namespace OMA.S_mse_2000333

theorem main :
    ∃ (F : Type) (_ : Field F),
      Nonempty (F ≃+* RatFunc (RatFunc F)) ∧ IsEmpty (F ≃+* RatFunc F) := by
  sorry

end OMA.S_mse_2000333
