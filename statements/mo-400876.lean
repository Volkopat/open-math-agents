import Mathlib

/-!
# Products of pairwise averaging matrices near the uniform matrix

Source: Joseph Van Name, https://mathoverflow.net/questions/400876 (CC BY-SA 4.0).
Credit: @connoranderson.

A factor may average any two permutation matrices, with its own real weight.
The neighborhood is taken in the ordinary finite-dimensional topology.
-/

namespace OMA.S_mo_400876

noncomputable def uniform (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => (n : ℝ)⁻¹

def products (n : ℕ) : Submonoid (Matrix (Fin n) (Fin n) ℝ) :=
  Submonoid.closure {A | ∃ (p q : Equiv.Perm (Fin n)) (t : ℝ),
    t ∈ Set.Icc 0 1 ∧ A = (1-t) • p.permMatrix ℝ + t • q.permMatrix ℝ}

theorem main : ∀ n : ℕ, 0 < n → ∃ U : Set (Matrix (Fin n) (Fin n) ℝ),
    IsOpen U ∧ uniform n ∈ U ∧ ∀ A ∈ U, A ∈ doublyStochastic ℝ (Fin n) → A ∈ products n := by
  sorry

end OMA.S_mo_400876
