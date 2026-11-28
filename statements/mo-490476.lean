import Mathlib.Logic.Function.Basic

/-!
# Duality of precomposition

Source: https://mathoverflow.net/questions/490476
Question by grge, April 4, 2025; CC BY-SA 4.0.

For a codomain with at least two elements, precomposition is injective exactly
when the original function is surjective, and surjective exactly when the
original function is injective. The nontrivial-codomain condition is necessary:
for a singleton codomain every precomposition map is bijective. The main
statement records both the literal counterexample and the corrected duality.
-/

namespace OMA.S_mo_490476

universe u v w

def precomp {X : Type u} {Y : Type v} {Z : Type w} (f : X → Y) :
    (Y → Z) → (X → Z) := fun g => g ∘ f

theorem main : (¬ (∀ (X Y Z : Type) (f : X → Y),
    (Function.Injective (precomp f : (Y → Z) → (X → Z)) ↔ Function.Surjective f) ∧
    (Function.Surjective (precomp f : (Y → Z) → (X → Z)) ↔ Function.Injective f))) ∧
    (∀ (X : Type u) (Y : Type v) (Z : Type w) [Nontrivial Z] (f : X → Y),
    (Function.Injective (precomp f : (Y → Z) → (X → Z)) ↔ Function.Surjective f) ∧
    (Function.Surjective (precomp f : (Y → Z) → (X → Z)) ↔ Function.Injective f)) := by
  sorry

end OMA.S_mo_490476
