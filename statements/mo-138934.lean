import Mathlib

/-!
# Irreducibility of trinomials over number fields

Source: Albertas, https://mathoverflow.net/questions/138934
Credit: @connoranderson

This is the posted question with A and B fixed as n varies.
-/

namespace OMA.S_mo_138934

open Polynomial
open scoped NumberField

theorem main : ∀ (K : Type) [Field K] [NumberField K] (A B : 𝓞 K),
    A ≠ 0 → B ≠ 0 → ∃ n : ℕ, 1 < n ∧
      Irreducible ((X : K[X]) ^ n + C (A : K) * X + C (B : K)) := by
  sorry

end OMA.S_mo_138934
