import Mathlib

/-!
# A071536: extending categorical composition to a semigroup

Source: https://oeis.org/A071536
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A071536): the composition in any category can be extended to a total,
associative operation, that is, to a semigroup.

Conventions:
* Categories are small (`C : Type` with `SmallCategory C`); morphisms are collected in the type
  `Σ X Y : C, X ⟶ Y`. The operation `mul g f` must equal `g ∘ f` (Mathlib's `f ≫ g`) whenever
  `f : X ⟶ Y` and `g : Y ⟶ Z` are composable.
-/

namespace OMA.S_oeis_a071536

open CategoryTheory

/-- All morphisms of `C`. -/
abbrev Arr (C : Type) [SmallCategory C] := Σ X Y : C, X ⟶ Y

theorem main :
    ∀ (C : Type) [SmallCategory C], ∃ mul : Arr C → Arr C → Arr C,
      (∀ a b c, mul (mul a b) c = mul a (mul b c)) ∧
      ∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z), mul ⟨Y, Z, g⟩ ⟨X, Y, f⟩ = ⟨X, Z, f ≫ g⟩ := by
  sorry

end OMA.S_oeis_a071536
