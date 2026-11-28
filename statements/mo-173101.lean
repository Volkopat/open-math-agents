import Mathlib

/-!
# When do unions and intersections of parametrized regions interchange?

Source: https://mathoverflow.net/questions/173101 (Arash, CC BY-SA 3.0).
Credit: @connoranderson

For a target point and parameter y, take the set of decisions x for which
that point lies in R(x,y). When these decision sets are compact convex
sets in k dimensions, the two sides coincide exactly when every point
passing all one-parameter tests passes every joint test of at most k+1
parameters. The number k+1 is sharp even for interval-valued regions with
continuous endpoints on a compact cube. The target space can be arbitrary.
-/

namespace OMA.S_mo_173101
noncomputable section

abbrev Space (k : ℕ) := Fin k → ℝ

def common {E Y Z : Type*} (X : Set E) (R : E → Y → Set Z) : Set Z :=
  {z | ∃ x ∈ X, ∀ y, z ∈ R x y}

def separate {E Y Z : Type*} (X : Set E) (R : E → Y → Set Z) : Set Z :=
  {z | ∀ y, ∃ x ∈ X, z ∈ R x y}

def tests {E Y Z : Type*} (X : Set E) (R : E → Y → Set Z) (m : ℕ) : Set Z :=
  {z | ∀ J : Finset Y, J.card ≤ m → ∃ x ∈ X, ∀ y ∈ J, z ∈ R x y}

def fibers {k : ℕ} {Y Z : Type*} (X : Set (Space k)) (R : Space k → Y → Set Z) : Prop :=
  ∀ z y, IsCompact {x | x ∈ X ∧ z ∈ R x y} ∧ Convex ℝ {x | x ∈ X ∧ z ∈ R x y}

def cube (k : ℕ) : Set (Space k) := Set.Icc 0 (fun _ => 1)

def cap {k : ℕ} (x : Space k) : Option (Fin k) → ℝ
  | none => (k:ℝ) - ∑ i, x i
  | some i => x i

def intervals {k : ℕ} (x : Space k) (j : Option (Fin k)) : Set ℝ :=
  Set.Icc 0 (min 1 (cap x j))

theorem main :
    (∀ (k : ℕ) (Y Z : Type) [Nonempty Y] (X : Set (Space k)) (R : Space k → Y → Set Z),
      fibers X R →
      common X R = tests X R (k+1) ∧
      (common X R = separate X R ↔ separate X R ⊆ tests X R (k+1))) ∧
    ∀ k : ℕ, 0 < k → fibers (cube k) intervals ∧
      (∀ j : Option (Fin k), Continuous (fun x : Space k => min 1 (cap x j))) ∧
      (∀ x ∈ cube k, ∀ j, (0:ℝ) ∈ intervals x j ∧ intervals x j ⊆ Set.Icc 0 1) ∧
      (1:ℝ) ∈ tests (cube k) intervals k ∧ (1:ℝ) ∉ common (cube k) intervals := by
  sorry

end
end OMA.S_mo_173101
