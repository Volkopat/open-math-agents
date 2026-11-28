import Mathlib

/-! Permanent variant of question 2 at https://mathoverflow.net/questions/288872 -/

namespace OMA.S_mo_288872

/-- A row set and a column set indexing one submatrix. -/
abbrev MinorIndex (m n : ℕ) := Finset (Fin m) × Finset (Fin n)

/-- The permanent of the selected square submatrix, and zero when the
row and column sets have unequal cardinalities. -/
def minorPermanent {K : Type*} [CommSemiring K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) K) (P : MinorIndex m n) : K :=
  if P.1.card = P.2.card then
    let rows := (List.finRange m).filter fun i => i ∈ P.1
    let cols := (List.finRange n).filter fun j => j ∈ P.2
    (rows.permutations'.map fun p => (List.zipWith M p cols).prod).sum
  else 0

/-- All order-k submatrices with nonzero permanent. -/
def permanentLayer {K : Type*} [CommSemiring K] [DecidableEq K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) K) (k : ℕ) : Finset (MinorIndex m n) :=
  Finset.univ.filter fun P => P.1.card = k ∧ P.2.card = k ∧ minorPermanent M P ≠ 0

/-- The proposed Sperner property for the nonvanishing permanent minors. -/
theorem main :
    ∀ (K : Type) [Field K] [DecidableEq K] (m n : ℕ)
      (M : Matrix (Fin m) (Fin n) K) (A : Finset (MinorIndex m n)),
      (∀ P ∈ A, minorPermanent M P ≠ 0) →
      (∀ P ∈ A, ∀ Q ∈ A, P.1 ⊆ Q.1 → P.2 ⊆ Q.2 → P = Q) →
      ∃ k : ℕ, A.card ≤ (permanentLayer M k).card := by
  sorry

end OMA.S_mo_288872
