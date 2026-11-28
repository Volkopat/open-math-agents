import Mathlib

/-!
# Maximizing the sum of pairwise distances in a compact planar region

Source: https://mathoverflow.net/questions/198221 (Andy Ludu, CC BY-SA 3.0).
Credit: @connoranderson

A support point in direction b maximizes the linear function x ↦ ⟪b,x⟫.
Optimize a score depending only on these support queries and a collection of
pair directions in the unit disk. The resulting independent choices of
support points maximize the original sum. Finite direction nets give a
finite enumeration with relative error at most their covering radius.
The construction applies to every nonempty compact planar set.
-/

namespace OMA.S_mo_198221
open Finset
open scoped RealInnerProductSpace
noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Configuration (n : ℕ) := Fin n → Plane
abbrev Directions (n : ℕ) := Fin n → Fin n → Plane

def energy {n : ℕ} (x : Configuration n) : ℝ := ∑ i, ∑ j, ‖x i-x j‖

def supportChoice (C : Set Plane) (p : Plane → Plane) : Prop :=
  ∀ b, p b ∈ C ∧ ∀ y ∈ C, ⟪b,y⟫ ≤ ⟪b,p b⟫

def resultant {n : ℕ} (u : Directions n) (i : Fin n) : Plane := ∑ j, (u i j-u j i)

def picked {n : ℕ} (p : Plane → Plane) (u : Directions n) : Configuration n :=
  fun i => p (resultant u i)

def score {n : ℕ} (p : Plane → Plane) (u : Directions n) : ℝ :=
  ∑ i, ⟪resultant u i,picked p u i⟫

def withinDisk {n : ℕ} (u : Directions n) : Prop := ∀ i j, ‖u i j‖ ≤ 1

def directionNet (ε : ℝ) (D : Finset Plane) : Prop :=
  (∀ d ∈ D, ‖d‖ ≤ 1) ∧ ∀ z : Plane, ‖z‖ ≤ 1 → ∃ d ∈ D, dist z d ≤ ε

def uses {n : ℕ} (D : Finset Plane) (u : Directions n) : Prop := ∀ i j, u i j ∈ D

theorem main :
    (∀ (ε : ℝ), 0 < ε → ∃ D : Finset Plane, directionNet ε D) ∧
    ∀ (C : Set Plane), IsCompact C → C.Nonempty → ∃ p : Plane → Plane,
      supportChoice C p ∧ ∀ n : ℕ,
      ((∃ u : Directions n, withinDisk u ∧ ∀ v : Directions n, withinDisk v → score p v ≤ score p u) ∧
       (∀ u : Directions n, withinDisk u → (∀ v : Directions n, withinDisk v → score p v ≤ score p u) →
        energy (picked p u) = score p u ∧ ∀ x : Configuration n,
          (∀ i, x i ∈ C) → energy x ≤ energy (picked p u))) ∧
      ∀ (ε : ℝ) (D : Finset Plane), directionNet ε D →
        (∃ u : Directions n, uses D u ∧ ∀ v : Directions n, uses D v → score p v ≤ score p u) ∧
        ∀ u : Directions n, uses D u → (∀ v : Directions n, uses D v → score p v ≤ score p u) →
          ∀ x : Configuration n, (∀ i, x i ∈ C) → (1-ε)*energy x ≤ energy (picked p u) := by
  sorry

end
end OMA.S_mo_198221
