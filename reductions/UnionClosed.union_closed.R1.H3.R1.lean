import OMAReductions.R_UnionClosed_union_closed_R1

/-!
# A restriction for each three-element member of a Frankl counterexample

Fix a three-element member S and group members by their part outside S. Among
the resulting families of traces on S, precisely six possible patterns have
mean trace size below three halves. Each consists of all subsets of one or two
of the three elements, together with S itself. If all three elements of S
occur in fewer than half of the family, at least three distinct outside parts
realize such patterns, or at least six when the family has even cardinality.
Each of those outside parts is itself a family member disjoint from S.

The second step retains the case in which every triple has enough witnesses.
-/
namespace OMA.R_UnionClosed_union_closed_R1_H3_R1

open Finset

def H1 : Prop := ∀ (m : ℕ) (A : Finset (Finset (Fin m))) (e : Fin 3 ↪ Fin m),
  UnionClosed.IsUnionClosed A → (univ : Finset (Fin 3)).map e ∈ A →
  (∀ i, 2 * (A.filter (fun X => e i ∈ X)).card < A.card) →
  let S := (univ : Finset (Fin 3)).map e
  let tr := fun X : Finset (Fin m) => (univ : Finset (Fin 3)).filter (fun i => e i ∈ X)
  let patterns := fun B : Finset (Fin m) => (A.filter (fun X => X \ S = B)).image tr
  let bad := A.filter fun B => Disjoint B S ∧ ∃ T ∈ (univ : Finset (Finset (Fin 3))),
    T.Nonempty ∧ T ≠ univ ∧ patterns B = insert univ T.powerset
  (if A.card % 2 = 0 then 6 else 3) ≤ bad.card

def H2 : Prop := ∀ (m : ℕ) (A : Finset (Finset (Fin m))), A ≠ {∅} →
  UnionClosed.IsUnionClosed A → (∀ X ∈ A, X.card ≠ 1 ∧ X.card ≠ 2) →
  (∃ X ∈ A, X ≠ ∅) →
  (∀ e : Fin 3 ↪ Fin m, (univ : Finset (Fin 3)).map e ∈ A →
    let S := (univ : Finset (Fin 3)).map e
    let tr := fun X : Finset (Fin m) => (univ : Finset (Fin 3)).filter (fun i => e i ∈ X)
    let patterns := fun B : Finset (Fin m) => (A.filter (fun X => X \ S = B)).image tr
    let bad := A.filter fun B => Disjoint B S ∧ ∃ T ∈ (univ : Finset (Finset (Fin 3))),
      T.Nonempty ∧ T ≠ univ ∧ patterns B = insert univ T.powerset
    (if A.card % 2 = 0 then 6 else 3) ≤ bad.card) →
  ∃ i : Fin m, (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => i ∈ X)).card

section Proof

theorem main : H1 → H2 → OMA.R_UnionClosed_union_closed_R1.H3 := by
  intro obstruction residual m A hn hu hs he
  by_contra h
  apply h
  apply residual m A hn hu hs he
  intro e hm
  apply obstruction m A e hu hm
  intro i
  have r : ((A.filter (fun X => e i ∈ X)).card : ℚ) < (1 / 2 : ℚ) * A.card :=
    lt_of_not_ge fun hi => h ⟨e i,hi⟩
  have r' : (2 : ℚ) * (A.filter (fun X => e i ∈ X)).card < A.card := by linarith
  exact_mod_cast r'

end Proof

end OMA.R_UnionClosed_union_closed_R1_H3_R1
