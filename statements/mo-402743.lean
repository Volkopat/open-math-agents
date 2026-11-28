import Mathlib

/-!
# Convex-hull and multiplicity conditions on maps of planar multisets

Source: Chris H, https://mathoverflow.net/questions/402743 (CC BY-SA 4.0).
Credit: @connoranderson. Gabriel C. Drummond-Cole gave a biased midpoint
counterexample for two inputs in the source comments. In higher degrees the
question's conditions are invariant under real-linear changes of coordinates.
Applying an anisotropic stretch to the roots of unity distinguishes the
ordinary derivative from a conjugated operator.
-/
namespace OMA.S_mo_402743
open Polynomial Set
abbrev Config (n : ℕ) := Sym ℂ n

def unordered {n : ℕ} (x : Fin n → ℂ) : Config n :=
  ⟨(List.ofFn x : Multiset ℂ), by simp⟩

noncomputable instance configTopology (n : ℕ) : TopologicalSpace (Config n) :=
  TopologicalSpace.coinduced (@unordered n) inferInstance

def points {n : ℕ} (S : Config n) : Set ℂ := {z | z ∈ S}

noncomputable def rootPoly {n : ℕ} (S : Config n) : ℂ[X] :=
  (S.val.map (fun z => X - C z)).prod

def admissible {n : ℕ} (D : Config (n+1) → Config n) : Prop :=
  Continuous D ∧ Function.Surjective D ∧
    (∀ S : Config (n+1), convexHull ℝ (points (D S)) ⊆ convexHull ℝ (points S)) ∧
    (∀ (S : Config (n+1)) (z : ℂ), z ∈ S →
      (D S).val.count z + 1 = S.val.count z)

def differentiates {n : ℕ} (D : Config (n+1) → Config n) : Prop :=
  ∀ S, (D S).val = (rootPoly S).derivative.roots

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ D F : Config (n+1) → Config n,
      admissible D ∧ differentiates D ∧ admissible F ∧ ¬ differentiates F := by
  sorry
end OMA.S_mo_402743
