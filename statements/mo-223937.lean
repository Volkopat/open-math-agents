import Mathlib

/-!
# Convex hull of simultaneous row and column permutations

Source: passerby51, https://mathoverflow.net/questions/223937 (CC BY-SA 3.0).
Credit: @connoranderson.

The orbit polytope is the image of an affine slice of the completely positive
cone of order n²+1. Its constraints contain no permutations and are linear in
the entries of the lifted matrix. This uses the completely positive formulation
of quadratic assignment by Povh and Rendl, https://optimization-online.org/2006/10/1502/.
The extra index is a normalizing coordinate. The defect is the squared norm of
a row or column sum of Gram factors minus that normalizing factor.
-/

namespace OMA.S_mo_223937
open Finset
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Idx (n : ℕ) := Option (Fin n × Fin n)
abbrev Lift (n : ℕ) := Matrix (Idx n) (Idx n) ℝ
def cell {n : ℕ} (i j : Fin n) : Idx n := some (i,j)

def orbit {n : ℕ} (X : Mat n) (s : Equiv.Perm (Fin n)) : Mat n := fun i j => X (s i) (s j)

noncomputable def gram {n : ℕ} {A : Type} [Fintype A] (v : Idx n → A → ℝ) : Lift n :=
  fun u w => ∑ a, v u a * v w a

def completelyPositive {n : ℕ} (M : Lift n) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (v : Idx n → A → ℝ), (∀ u a, 0≤v u a) ∧ M=gram v

noncomputable def defect {n : ℕ} (M : Lift n) (b : Fin n → Idx n) : ℝ :=
  (∑ j, ∑ k, M (b j) (b k)) - 2 * (∑ j, M (b j) none) + M none none

def feasible {n : ℕ} (M : Lift n) : Prop :=
  completelyPositive M ∧ M none none = 1 ∧
  (∀ i, defect M (fun j => cell i j) = 0) ∧
  (∀ j, defect M (fun i => cell i j) = 0) ∧
  (∀ i j k, j≠k → M (cell i j) (cell i k) = 0)

noncomputable def project {n : ℕ} (X : Mat n) (M : Lift n) : Mat n :=
  fun i k => ∑ j, ∑ l, X j l * M (cell i j) (cell k l)

theorem main : ∀ (n : ℕ) (X Y : Mat n),
    Y ∈ convexHull ℝ (Set.range (orbit X)) ↔ ∃ M : Lift n, feasible M ∧ Y=project X M := by
  sorry
end OMA.S_mo_223937
