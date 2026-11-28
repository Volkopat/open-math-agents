import Mathlib

/-! Source: https://mathoverflow.net/questions/115849 (question 2). -/

namespace OMA.S_mo_115849

/-- The standard open simplex from the question. -/
def levinsonSimplex (n : ℕ) :=
  {x : Fin n → ℝ // (∀ i, 0 < x i) ∧ (∑ i, x i) < 1}

/-- The inequality attached to a facet, written as the total sum minus twice its facet sum. -/
def levinsonFacet {n : ℕ} (A : Finset (Fin n)) (x : levinsonSimplex n) : Prop :=
  (1 / 2 : ℝ) < (∑ i, x.val i) - 2 * ∑ i ∈ A, x.val i

/-- Product of the facet indicators: one exactly when all facet inequalities hold. -/
noncomputable def levinsonIndicator {n : ℕ} (S : Finset (Finset (Fin n)))
    (x : levinsonSimplex n) : ℂ := by
  classical
  exact if ∀ A ∈ S, levinsonFacet A x then 1 else 0

/-- The set of distinct nonzero indicators coming from families of maximal faces. -/
def levinsonFeasible (n : ℕ) : Set (levinsonSimplex n → ℂ) :=
  {g | ∃ S : Finset (Finset (Fin n)),
    (∀ A ∈ S, ∀ B ∈ S, A ⊆ B → A = B) ∧
      (∃ x, levinsonIndicator S x = 1) ∧ g = levinsonIndicator S}

/-- Are the feasible indicators of simplicial complexes linearly independent? -/
theorem main :
    ∀ n : ℕ, LinearIndepOn ℂ id (levinsonFeasible n) := by
  sorry

end OMA.S_mo_115849
