import Mathlib

/-!
# When does a partial isometry of the sign cube extend to a cube symmetry?

Source: https://mathoverflow.net/questions/348427 (D_809, CC BY-SA 4.0).
Credit: @connoranderson

Use distinct input vertices, as required for a finite maximum; repeating a
matched pair never adds a constraint. Use the source's final formulation:
no signed coordinate permutation may realize the prescribed correspondence.
In dimensions at most three every such correspondence extends. Starting
in dimension four the largest nonextendible correspondence has half of the
vertices. A matrix realizing a correspondence need not be its only extension.
-/

namespace OMA.S_mo_348427
open Matrix Finset
noncomputable section

abbrev Vertex (n : ℕ) := Fin n → Bool
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def sign {n : ℕ} (v : Vertex n) (i : Fin n) : ℝ := if v i then 1 else -1

def admissible {n : ℕ} (Q : Mat n) (S : Finset (Vertex n)) : Prop :=
  ∀ v ∈ S, ∃ w : Vertex n, Q *ᵥ sign v = sign w

def agrees {n : ℕ} (Q : Mat n) (S : Finset (Vertex n)) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (e : Vertex n),
    ∀ v ∈ S, ∀ i, (Q *ᵥ sign v) i = sign e i * sign v (σ i)

theorem main :
    (∀ n : ℕ, n ≤ 3 → ∀ (Q : Mat n) (S : Finset (Vertex n)),
      Qᵀ*Q = 1 → admissible Q S → agrees Q S) ∧
    (∀ n : ℕ, 4 ≤ n →
      (∀ (Q : Mat n) (S : Finset (Vertex n)), Qᵀ*Q = 1 → admissible Q S →
        ¬ agrees Q S → 2*S.card ≤ 2^n) ∧
      ∃ (Q : Mat n) (S : Finset (Vertex n)), Qᵀ*Q = 1 ∧ admissible Q S ∧
        ¬ agrees Q S ∧ 2*S.card = 2^n) := by
  sorry

end
end OMA.S_mo_348427
