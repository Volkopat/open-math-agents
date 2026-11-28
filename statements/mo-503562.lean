import Mathlib

/-!
# Determinant of a union-closed family of sets

Fabius Wiesner asks for the exact exponent of each variable in the determinant
of the matrix whose entries are the squarefree monomials of pairwise unions.
The family and its ground set are indexed by finite types of sizes `n` and `q`.

Source: https://mathoverflow.net/questions/503562
Credit: @GitHoobar
-/

namespace OMA.S_mo_503562

open scoped BigOperators

/-- The number of members of the indexed family containing an element. -/
def frequency {n q : ℕ} (A : Fin n → Finset (Fin q)) (k : Fin q) : ℕ :=
  (Finset.univ.filter fun i => k ∈ A i).card

/-- Entry `(i, j)` is the product of the distinct variables in `A i ∪ A j`. -/
noncomputable def unionMatrix {n q : ℕ} (A : Fin n → Finset (Fin q)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin q) ℤ) :=
  fun i j => ∏ k ∈ A i ∪ A j, MvPolynomial.X k

/-- The frequencies give exactly the common variable factors of the determinant. -/
theorem main :
    ∀ (n q : ℕ) (A : Fin n → Finset (Fin q)),
    Function.Injective A →
    (∀ i j, ∃ t, A t = A i ∪ A j) →
    (∀ k : Fin q, ∃ i, k ∈ A i) →
    ∃ P : MvPolynomial (Fin q) ℤ,
      (unionMatrix A).det = P * (∏ k, MvPolynomial.X k ^ frequency A k) ∧
      ∀ k : Fin q, ¬ MvPolynomial.X k ∣ P := by
  sorry

end OMA.S_mo_503562
