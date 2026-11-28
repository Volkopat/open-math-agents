import Mathlib

/-!
# MathOverflow 211562

Source: https://mathoverflow.net/questions/211562
-/

namespace OMA.S_mo_211562

open FirstOrder FirstOrder.Language

inductive PureGroupSymbol : ℕ → Type
  | identity : PureGroupSymbol 0
  | inverse : PureGroupSymbol 1
  | multiply : PureGroupSymbol 2

def pureGroupLanguage : Language where
  Functions := PureGroupSymbol
  Relations := fun _ => Empty

abbrev pureGroupStructure (G : Type) [Group G] : pureGroupLanguage.Structure G where
  funMap f args := match f with
    | .identity => 1
    | .inverse => (args 0)⁻¹
    | .multiply => args 0 * args 1
  RelMap r _ := Empty.elim r

def DefinesSubgroupWithoutParameters {G : Type} [Group G] (φ : pureGroupLanguage.Formula Unit)
    (H : Subgroup G) : Prop :=
  let _ := pureGroupStructure G
  ∀ x : G, x ∈ H ↔ φ.Realize (fun _ => x)

theorem main : ∀ (G : Type) [Group G] (H : Subgroup G),
    (∃ φ : pureGroupLanguage.Formula Unit, DefinesSubgroupWithoutParameters φ H) →
      H.Characteristic ∧ H.Normal := by
  sorry

end OMA.S_mo_211562
