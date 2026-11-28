import Mathlib

/-!
# Convex feasible sets of homogeneous quadratic matrix inequalities

Source: fanfare, https://mathoverflow.net/questions/281163 (CC BY-SA 3.0).
Credit: @connoranderson.

For the homogeneous constraint in the question, a convex feasible set must
be a linear subspace. It then admits a diagonal linear matrix inequality.
A Gram factorization of the quadratic coefficients supplies one explicit
sufficient condition, under which the equations defining the subspace are
read directly from the factors.
-/

namespace OMA.S_mo_281163

noncomputable def quad {n q : ℕ} (M : Fin q → Fin q → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun a b => ∑ i, ∑ j, x i * M a b i j * x j

noncomputable def lmi {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (x : Fin n → ℝ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℝ :=
  Matrix.diagonal (fun i => if i.2 then L x i.1 else -L x i.1)

noncomputable def gramCoeff {n q r : ℕ} (F : Fin r → Fin q → Fin n → ℝ)
    (a b : Fin q) : Matrix (Fin n) (Fin n) ℝ := fun i j => ∑ t, F t a i * F t b j

noncomputable def symmGram {n q r : ℕ} (F : Fin r → Fin q → Fin n → ℝ)
    (a b : Fin q) : Matrix (Fin n) (Fin n) ℝ :=
  (1/2 : ℝ) • (gramCoeff F a b + gramCoeff F b a)

theorem main : (∀ {n q : ℕ} (M : Fin q → Fin q → Matrix (Fin n) (Fin n) ℝ),
    (∀ a b, M a b = M b a) →
    let S := {x : Fin n → ℝ | (-(quad M x)).PosSemidef}
    (Convex ℝ S ↔ ∃ W : Submodule ℝ (Fin n → ℝ), S = (W : Set (Fin n → ℝ))) ∧
    (Convex ℝ S → ∃ L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ),
      ∀ x, x ∈ S ↔ (lmi L x).PosSemidef)) ∧
    ∀ {n q r : ℕ} (F : Fin r → Fin q → Fin n → ℝ) (x : Fin n → ℝ),
      (∀ a b, symmGram F a b = symmGram F b a) ∧
      ((-(quad (symmGram F) x)).PosSemidef ↔ ∀ t a, (∑ i, F t a i * x i) = 0) := by
  sorry

end OMA.S_mo_281163
