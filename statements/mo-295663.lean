import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Representable integer matrices

Source: https://mathoverflow.net/questions/295663

A pair of integer vectors is the pair of column and row sums of an integer
matrix if and only if the two vectors have equal total sum. The theorem covers
every dimension, including the empty matrix.
-/

namespace OMA.S_mo_295663

open scoped BigOperators

/-- `C` and `R` are representable by the column and row sums of an integer matrix. -/
def Representable {n : ℕ} (C R : Fin n → ℤ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℤ,
    (∀ j, ∑ i, M i j = C j) ∧ (∀ i, ∑ j, M i j = R i)

theorem main : ∀ (n : ℕ) (C R : Fin n → ℤ),
    Representable C R ↔ ∑ i, C i = ∑ i, R i := by
  sorry

end OMA.S_mo_295663
