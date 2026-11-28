import Mathlib

/-!
# MathOverflow 85848

Source: https://mathoverflow.net/questions/85848
-/

namespace OMA.S_mo_85848

open Submodule

def tailIntersection {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (W : Fin n → Submodule K V) (i : ℕ) : Submodule K V :=
  ⨅ j : Fin n, ⨅ _ : i ≤ j.val, W j

theorem main : ∀ (p d : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [Module.Finite (ZMod p) V], Module.finrank (ZMod p) V = d →
      ¬ ∃ W : Fin (d + 1) → Submodule (ZMod p) V, Function.Injective W ∧
        (∀ i, Module.finrank (ZMod p) (W i) = d - 1) ∧
        (∀ i : Fin d, W i.castSucc ⊔ tailIntersection W (i.val + 1) = ⊤) ∧
        ∃ x : V, ∀ i, x ∉ W i := by
  sorry

end OMA.S_mo_85848
