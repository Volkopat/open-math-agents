import Mathlib

/-!
# A finite test for a common permutation basis

Source: as2457, https://mathoverflow.net/questions/354536 (CC BY-SA).
Nick Gill proposed testing possible permutations by their action on the basis.
Denis Serre gave group-order and trace filters. Here each candidate pair is
tested by a linear system and finitely many determinants. Credit: @connoranderson.
-/
namespace OMA.S_mo_354536
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)
def common {n} (A B : Mat n) : Prop :=
  ∃ (U : unitary (Mat n)) (σ τ : Perm n),
    (U : Mat n)*A*(U : Mat n)ᴴ=σ.permMatrix ℂ ∧ (U : Mat n)*B*(U : Mat n)ᴴ=τ.permMatrix ℂ

def inter {n} (A B : Mat n) (σ τ : Perm n) : Submodule ℂ (Mat n) where
  carrier := {X | X*A=σ.permMatrix ℂ*X ∧ X*B=τ.permMatrix ℂ*X}
  zero_mem' := by simp
  add_mem' := by rintro X Y ⟨ha,hb⟩ ⟨hc,hd⟩; exact ⟨by rw [Matrix.add_mul,Matrix.mul_add,ha,hc],by rw [Matrix.add_mul,Matrix.mul_add,hb,hd]⟩
  smul_mem' := by rintro c X ⟨ha,hb⟩; exact ⟨by rw [Matrix.smul_mul,Matrix.mul_smul,ha],by rw [Matrix.smul_mul,Matrix.mul_smul,hb]⟩

noncomputable def pencil {n d : ℕ} (v : Fin d → Mat n) : MvPolynomial (Fin d) ℂ :=
  (Matrix.of (fun i j => ∑ l, MvPolynomial.X l * MvPolynomial.C (v l i j))).det
abbrev BasisFor {n} (A B : Mat n) (σ τ : Perm n) :=
  Module.Basis (Fin (Module.finrank ℂ (inter A B σ τ))) ℂ (inter A B σ τ)
noncomputable def basisMatrices {n} {A B : Mat n} {σ τ : Perm n} (b : BasisFor A B σ τ) :
    Fin (Module.finrank ℂ (inter A B σ τ)) → Mat n := fun j => b j

theorem main : ∀ (n : ℕ) (A B : Mat n), A ∈ unitary (Mat n) → B ∈ unitary (Mat n) →
  ∀ bases : ∀ σ τ, BasisFor A B σ τ,
  (common A B ↔ ∃ σ τ : Perm n, pencil (basisMatrices (bases σ τ)) ≠ 0) ∧
  (common A B ↔ ∃ (σ τ : Perm n) (t : Fin (Module.finrank ℂ (inter A B σ τ)) → Fin (n+1)),
    (∑ j, (t j : ℂ) • basisMatrices (bases σ τ) j).det ≠ 0) := by
  sorry
end OMA.S_mo_354536
