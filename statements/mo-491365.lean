import Mathlib

/-!
# Comparing Gram matrices under different positive definite deformations

Source: nagato30, https://mathoverflow.net/questions/491365 (CC BY-SA 4.0).
Credit: @connoranderson.

Comparison constants may depend on the fixed deformations and the dimensions.
Every positive definite inverse square root is an invertible linear operator.
The two fixed operators in the counterexample are the identity and the positive
diagonal matrix with entries 1 and 2. They are inverse square roots of the
identity and the diagonal covariance with entries 1 and 1/4.
-/

namespace OMA.S_mo_491365

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def largest {n m : ℕ} (x : Fin (m+1) → E n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (Matrix.isHermitian_gram ℝ x).eigenvalues

noncomputable def smallest {n m : ℕ} (x : Fin (m+1) → E n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (Matrix.isHermitian_gram ℝ x).eigenvalues

noncomputable def changeTwo (x : Fin 2 → E 2) : Fin 2 → E 2 :=
  ![x 0, !₂[x 1 0, 2*x 1 1]]

theorem main :
    (∀ (n m : ℕ) (T : Fin (m+1) → E n ≃L[ℝ] E n), ∃ c : ℝ, 0<c ∧ ∃ C : ℝ, 0<C ∧
      ∀ x : Fin (m+1) → E n, c*largest (fun i => T i (x i)) ≤ largest x ∧
        largest x ≤ C*largest (fun i => T i (x i))) ∧
    (∀ K : ℝ, 0<K → ∃ x : Fin 2 → E 2, LinearIndependent ℝ x ∧
      LinearIndependent ℝ (changeTwo x) ∧
      K*(Matrix.gram ℝ x).det < (Matrix.gram ℝ (changeTwo x)).det ∧
      K*smallest x < smallest (changeTwo x)) ∧
    (∀ K : ℝ, 0<K → ∃ x : Fin 2 → E 2, LinearIndependent ℝ x ∧
      LinearIndependent ℝ (changeTwo x) ∧
      K*(Matrix.gram ℝ (changeTwo x)).det < (Matrix.gram ℝ x).det ∧
      K*smallest (changeTwo x) < smallest x) := by
  sorry

end OMA.S_mo_491365
