import Mathlib

/-!
# MathOverflow 79461: do four cone properties characterize positive Hermitian matrices?

Source: https://mathoverflow.net/questions/79461
Question by MathOverflow user spelas; source text licensed CC BY-SA 3.0.
Credit: @iancbaer (agent: Codex)

The source specifies nonnegative eigenvalues, not all zero. Accordingly the
reference cone is the nonzero positive semidefinite Hermitian matrices, NOT
just the positive definite matrices. Its question asks whether a different
subset can satisfy (i) addition closure, (ii) positive real scaling closure,
(iii) nonnegative spectrum with a nonzero eigenvalue, and (iv) P-P+iP-iP = M_n(C),
without being tPt⁻¹ for any invertible t.

We state the affirmative answer in every dimension at least two, parametrized
as n+2. (Dimension one is exceptional: property (iii), positive scaling, and
(iv) force precisely the positive real ray.) `ComplexOrder` makes `0 ≤ z`
mean that z is real and nonnegative. Units encode arbitrary invertible t;
the action below is similarity tAt⁻¹, not congruence tAt*.
-/

open scoped ComplexOrder
namespace OMA.S_mo_79461

abbrev Mat (n : ℕ) := Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ

def referenceCone (n : ℕ) : Set (Mat n) :=
  {A | A.PosSemidef ∧ A ≠ 0}

def ConeConditions {n : ℕ} (C : Set (Mat n)) : Prop :=
  (∀ A ∈ C, ∀ B ∈ C, A + B ∈ C) ∧
  (∀ r : ℝ, 0 < r → ∀ A ∈ C, r • A ∈ C) ∧
  (∀ A ∈ C, (∀ z ∈ spectrum ℂ A, 0 ≤ z) ∧ ∃ z ∈ spectrum ℂ A, z ≠ 0) ∧
  (∀ X : Mat n, ∃ A ∈ C, ∃ B ∈ C, ∃ D ∈ C, ∃ E ∈ C,
    X = A - B + Complex.I • D - Complex.I • E)

/-- A different cone with all four stated properties exists in every dimension ≥ 2. -/
theorem main : ∀ n : ℕ, ∃ C : Set (Mat n), ConeConditions C ∧
    ∀ U : (Mat n)ˣ, C ≠
      (fun A : Mat n => (U : Mat n) * A * (↑U⁻¹ : Mat n)) '' referenceCone n := by
  sorry

end OMA.S_mo_79461
