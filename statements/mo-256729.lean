import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi

open scoped BigOperators

namespace OMA.S_mo_256729

/-- Exhaustive finite search for a nonnegative integral solution of `A x = b`.
The bound on every searched coordinate is the sum of the entries of `b`. -/
def hasSolution {m n : ℕ} (A : Fin m → Fin n → ℕ) (b : Fin m → ℕ) : Bool :=
  decide (∃ x : Fin n → Fin ((∑ i, b i) + 1),
    ∀ i, ∑ j, A i j * (x j).val = b i)

/-- Every nonnegative integral system is equivalent to a finite search, and the
explicit Boolean decision procedure is correct for all dimensions and inputs. -/
theorem main : ∀ (m n : ℕ) (A : Fin m → Fin n → ℕ) (b : Fin m → ℕ),
    ((∃ x : Fin n → ℕ, ∀ i, ∑ j, A i j * x j = b i) ↔
      ∃ x : Fin n → Fin ((∑ i, b i) + 1), ∀ i, ∑ j, A i j * (x j).val = b i) ∧
    (hasSolution A b = true ↔
      ∃ x : Fin n → ℕ, ∀ i, ∑ j, A i j * x j = b i) := by sorry

end OMA.S_mo_256729
