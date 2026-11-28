import Mathlib

/-!
# Erdős Problem 62

Source: https://www.erdosproblems.com/62
Credit: @shc261392

The source asks: if `G₁, G₂` are two graphs with chromatic number `ℵ₁`, must there exist a graph
`G` whose chromatic number is `4` (or even `ℵ₀`) which is a subgraph of both `G₁` and `G₂`?

Reading used here:
* This file states the main question, with chromatic number `4`, in its affirmative form (as
  formal-conjectures does for the companion question Erdős 740). A proof of `main` answers it yes;
  a proof of `¬ main` answers it no. The stronger `ℵ₀` variant is not stated here.
* Chromatic number `ℵ₁` is `chromaticCardinal G = ℵ₁`, where `chromaticCardinal G` is the least
  cardinality of a colour set admitting a proper colouring (the same definition as
  formal-conjectures' `SimpleGraph.chromaticCardinal`, restated here because a statement file
  imports Mathlib only).
* "`G` is a subgraph of `Gᵢ`" means `G` is isomorphic to a (not necessarily induced) subgraph of
  `Gᵢ`, i.e. there is an injective graph homomorphism `G →g Gᵢ`.
* All vertex types are taken in `Type` (universe 0).
-/

namespace OMA.S_erdos_62

open Cardinal

/-- The chromatic cardinal of `G`: the least cardinality of a colour type admitting a proper
colouring of `G`. -/
noncomputable def chromaticCardinal {V : Type} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

theorem main :
    ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
      chromaticCardinal G₁ = ℵ₁ → chromaticCardinal G₂ = ℵ₁ →
        ∃ (W : Type) (G : SimpleGraph W) (f₁ : G →g G₁) (f₂ : G →g G₂),
          Function.Injective f₁ ∧ Function.Injective f₂ ∧ G.chromaticNumber = 4 := by
  sorry

end OMA.S_erdos_62
