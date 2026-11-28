import OMAReductions.R_UnionClosed_union_closed_R1

/-!
# Families of lattice boxes, in arbitrary dimension

If a single injective labeling identifies each nonempty member with an entire
lattice box, a pair of equal or adjacent grid points meets every nonempty
member. Union closure then implies that an element belongs to at least half
of the family. The residual covers the families without such a labeling.
-/
namespace OMA.R_UnionClosed_union_closed_R1_H3_R2

open Finset

def H1 : Prop := ∀ (m d : ℕ) (A : Finset (Finset (Fin m))) (e : Fin m ↪ (Fin d → ℤ)),
  UnionClosed.IsUnionClosed A → (∃ X ∈ A, X ≠ ∅) →
  (∀ X ∈ A, X.Nonempty → ∃ lo hi : Fin d → ℤ, ∀ z : Fin d → ℤ,
    (∃ x ∈ X, e x = z) ↔ ∀ j, lo j ≤ z j ∧ z j ≤ hi j) →
  ∃ i : Fin m, (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => i ∈ X)).card

def H2 : Prop := ∀ (m : ℕ) (A : Finset (Finset (Fin m))), A ≠ {∅} →
  UnionClosed.IsUnionClosed A → (∀ X ∈ A, X.card ≠ 1 ∧ X.card ≠ 2) →
  (∃ X ∈ A, X ≠ ∅) →
  (¬ ∃ (d : ℕ) (e : Fin m ↪ (Fin d → ℤ)), ∀ X ∈ A, X.Nonempty →
    ∃ lo hi : Fin d → ℤ, ∀ z : Fin d → ℤ,
      (∃ x ∈ X, e x = z) ↔ ∀ j, lo j ≤ z j ∧ z j ≤ hi j) →
  ∃ i : Fin m, (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => i ∈ X)).card

section Proof

theorem main : H1 → H2 → OMA.R_UnionClosed_union_closed_R1.H3 := by
  intro boxes residual m A hn hu hs he
  classical
  by_cases geometric : ∃ (d : ℕ) (e : Fin m ↪ (Fin d → ℤ)), ∀ X ∈ A, X.Nonempty →
    ∃ lo hi : Fin d → ℤ, ∀ z : Fin d → ℤ,
      (∃ x ∈ X, e x = z) ↔ ∀ j, lo j ≤ z j ∧ z j ≤ hi j
  · obtain ⟨d,e,h⟩ := geometric
    exact boxes m d A e hu he h
  · exact residual m A hn hu hs he geometric

end Proof

end OMA.R_UnionClosed_union_closed_R1_H3_R2
