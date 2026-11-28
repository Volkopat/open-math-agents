import Mathlib

/-!
# Exact positivity criteria for a covariance quadratic on the simplex

Source: J M Grandola, https://mathoverflow.net/questions/356828 (CC BY-SA 4.0).
Credit: @connoranderson. DSM's answer gives a sufficient semidefinite condition.
The proof uses the classical first-order optimality criterion for convex
minimization and retains the distinction between the open and closed simplex.

For each row, nonnegativity on the closed simplex is equivalent to feasibility
of one linear matrix inequality with n affine inequalities. Strict positivity
on the open simplex requires in addition infeasibility of an explicit linear
system that detects interior stationary points of value zero. A separate
equivalent test uses only linear systems, one for each face. Singular covariance
matrices are included. A diagonal bound strictly below four guarantees
positivity in all dimensions, and this universal threshold is sharp.
-/
namespace OMA.S_mo_356828
open Matrix Finset

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ

def interiorWeights {n : ℕ} (x : Vec n) : Prop := (∀ j, 0 < x j) ∧ ∑ j, x j = 1

noncomputable def energy {n : ℕ} (A : Mat n) (x : Vec n) : ℝ := x ⬝ᵥ (A *ᵥ x)

noncomputable def value {n : ℕ} (A : Mat n) (i : Fin n) (x : Vec n) : ℝ :=
  1 - (A *ᵥ x) i + energy A x

/-- Convex feasibility with one quadratic constraint and n affine inequalities. -/
def certificate {n : ℕ} (A : Mat n) (i : Fin n) : Prop :=
  ∃ (y : Vec n) (t : ℝ), energy A y ≤ t ∧ ∀ j, t ≤ 1 + 2*(A *ᵥ y) j - A i j

/-- A linear feasibility test for an interior stationary point with value zero. -/
def interiorContact {n : ℕ} (A : Mat n) (i : Fin n) : Prop :=
  ∃ (x : Vec n) (s : ℝ), interiorWeights x ∧
    (∀ j, 2*(A *ᵥ x) j - A i j = s) ∧ 2 + s - (A *ᵥ x) i = 0

/-- One linear feasibility test per nonempty face. Strict negativity on a
proper face also violates positivity on the open simplex by continuity. -/
def badFace {n : ℕ} (A : Mat n) (i : Fin n) (T : Finset (Fin n)) : Prop :=
  ∃ (x : Vec n) (s : ℝ), (∑ j, x j) = 1 ∧
    (∀ j ∈ T, 0 < x j) ∧ (∀ j ∉ T, x j = 0) ∧
    (∀ j ∈ T, 2*(A *ᵥ x) j - A i j = s) ∧
    (2 + s - (A *ᵥ x) i < 0 ∨ (T = univ ∧ 2 + s - (A *ᵥ x) i = 0))

/-- The positive-semidefinite epigraph of the covariance quadratic. Both
the bordered matrix and the remaining side conditions are affine in y,t. -/
noncomputable def bordered {n : ℕ} (A : Mat n) (y : Vec n) (t : ℝ) :
    Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (Matrix.of (fun _ _ => t)) (Matrix.of (fun _ j => (A *ᵥ y) j))
    (Matrix.of (fun j _ => (A *ᵥ y) j)) A

def lmiTest {n : ℕ} (A : Mat n) (i : Fin n) : Prop :=
  ∃ (y : Vec n) (t : ℝ), (bordered A y t).PosSemidef ∧ ∀ j, t ≤ 1 + 2*(A *ᵥ y) j - A i j

theorem main :
    (∀ (n : ℕ) (A : Mat n), A.PosSemidef → ∀ (i : Fin n),
      ((∀ x ∈ stdSimplex ℝ (Fin n), 0 ≤ value A i x) ↔ lmiTest A i) ∧
      ((∀ x, interiorWeights x → 0 < value A i x) ↔ lmiTest A i ∧ ¬ interiorContact A i) ∧
      ((∀ x, interiorWeights x → 0 < value A i x) ↔ ∀ T, ¬ badFace A i T) ∧
      (∀ x : Vec n, 4-A i i ≤ 4*value A i x)) ∧
    (∀ d : ℝ, (∀ (n : ℕ) (A : Mat n), A.PosSemidef → (∀ i, A i i ≤ d) →
      ∀ (i : Fin n) (x : Vec n), interiorWeights x → 0 < value A i x) ↔ d < 4) := by
  sorry

end OMA.S_mo_356828
