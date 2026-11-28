import OMAReductions.R_UnionClosed_union_closed_variants_univ_card_R1

-- Reduction UnionClosed.union_closed.variants.univ_card.R1.H1.R1 of step UnionClosed.union_closed.variants.univ_card.R1.H1
-- Credit: @Ciphore

/-!
# Split the minimum-three case of the twelve-element Frankl theorem by multiplicity of triangles

Vučković and Živković prove the minimum-three case (row 25 of Table I) only for
families whose three-element member is unique: whenever two distinct three-element
sets are present, their intersection pattern is a configuration already covered by
the earlier rows 17, 18 and 22 of the table.  Neither hypothesis is a restatement
of the target: the first is the dense case where additional three-sets supply extra
union-closure constraints, while the second is the sparse case treated by the
hypercube share computation with the corrected smallest shares.
-/

namespace OMA.R_UnionClosed_union_closed_variants_univ_card_R1_H1_R1
open Finset UnionClosed
open scoped Classical

/-- Dense case: some pair of distinct three-element members is present. -/
def H1 : Prop :=
  ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧ S.card = 3 ∧ T.card = 3) →
    (∀ S ∈ F, S.Nonempty → 3 ≤ S.card) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

/-- Sparse case: the three-element member is unique. -/
def H2 : Prop :=
  ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∃ S ∈ F, S.card = 3) →
    (∀ S ∈ F, ∀ T ∈ F, S.card = 3 → T.card = 3 → S = T) →
    (∀ S ∈ F, S.Nonempty → 3 ≤ S.card) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

theorem main : H1 → H2 → OMA.R_UnionClosed_union_closed_variants_univ_card_R1.H1 := by
  intro dense sparse F closed empty full existsThree minimal
  by_cases multi : ∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧ S.card = 3 ∧ T.card = 3
  · exact dense F closed empty full multi minimal
  · apply sparse F closed empty full existsThree _ minimal
    intro S hS T hT s t
    by_contra ne
    exact multi ⟨S, hS, T, hT, ne, s, t⟩

end OMA.R_UnionClosed_union_closed_variants_univ_card_R1_H1_R1
