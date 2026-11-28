import Mathlib

/-!
# Simultaneous containment of unions and intersections of translated compacts

In a topological group, suppose the union and intersection of two left-translated
closed compact sets are contained in corresponding translates of their original
union and intersection. Must both inclusions be equalities?

[MathOverflow question](https://mathoverflow.net/questions/137602/can-closed-compacts-in-a-topological-group-behave-paradoxically-with-respect-t)
-/

open scoped Pointwise

namespace OMA.S_mo_137602

theorem main :
    ∀ (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (A B : Set G) (a b unionShift intersectionShift : G),
      IsCompact A → IsClosed A → IsCompact B → IsClosed B →
      a • A ∪ b • B ⊆ unionShift • (A ∪ B) →
      a • A ∩ b • B ⊆ intersectionShift • (A ∩ B) →
      a • A ∪ b • B = unionShift • (A ∪ B) ∧
        a • A ∩ b • B = intersectionShift • (A ∩ B) := by
  sorry

end OMA.S_mo_137602
