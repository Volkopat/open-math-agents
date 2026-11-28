import Mathlib

/-!
# MathOverflow 218348

Source: https://mathoverflow.net/questions/218348
-/

namespace OMA.S_mo_218348

open Finset Polynomial
open scoped BigOperators

noncomputable def partialOrderFactor {p : ℕ} (A : Finset (ZMod p)) (a : ZMod p) :
    Polynomial (ZMod p) :=
  ∏ b ∈ A.erase a, (X - C b)

theorem main : ∀ p m : ℕ, p.Prime → 0 < m → p ≡ 1 [MOD m] →
      ∀ A : Finset (ZMod p), (∀ a : ZMod p, a ∈ A ↔ orderOf a=m) →
        A.card=m.totient →
        ∀ a ∈ A, ∀ i < m.totient, (partialOrderFactor A a).coeff i ≠ 0 := by
  sorry

end OMA.S_mo_218348
