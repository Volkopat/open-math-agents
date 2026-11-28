import OMAStatements.S_mo_472069
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

/-!
Counterexample in the symmetry group of a regular pentagon.
Source: https://mathoverflow.net/questions/472069
Credit: @zarnab222-dev
-/

open scoped Pointwise
open DihedralGroup OMA.S_mo_472069

namespace MO472069

abbrev G := DihedralGroup 5

def A : Finset G := {r 1, r 4, sr 1, sr 4}

def H : Subgroup G where
  carrier := {g | g = 1 ∨ g = sr 0}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> decide
  inv_mem' := by
    rintro x (rfl | rfl) <;> decide

lemma generates : Subgroup.closure (A : Set G) = ⊤ := by
  apply top_unique
  intro x _
  have hall : ∀ g : G, g ∈ A ∨ g ∈ A * A := by decide +kernel
  rcases hall x with hx | hx
  · exact Subgroup.subset_closure hx
  · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ha) (Subgroup.subset_closure hb)

lemma unionH : UnionLeftCosets ((A * A : Finset G) : Set G) H := by
  change ∀ x : G, x ∈ A * A → ∀ h : G, (h = 1 ∨ h = sr 0) → x * h ∈ A * A
  decide +kernel

lemma greatest (K : Subgroup G) (hK : UnionLeftCosets ((A * A : Finset G) : Set G) K) :
    K ≤ H := by
  have test : ∀ h : G, (∀ x : G, x ∈ A * A → x * h ∈ A * A) → (h = 1 ∨ h = sr 0) := by
    decide +kernel
  intro h hh
  exact test h (fun x hx => hK x hx h hh)

theorem counter : ¬ H.Normal := by
  intro hn
  have h := hn.conj_mem (sr 0) (Or.inr rfl) (r 1)
  have bad : ¬ ((r 1 : G) * sr 0 * (r 1)⁻¹ = 1 ∨ (r 1 : G) * sr 0 * (r 1)⁻¹ = sr 0) := by decide
  exact bad h

end MO472069

open MO472069

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_472069.main) := by
  intro claim
  exact counter (claim G A H generates unionH (fun K _ hK => greatest K hK) (by decide +kernel))
