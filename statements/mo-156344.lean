import Mathlib

open scoped ContDiff

namespace OMA.S_mo_156344

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A regular smooth parametrization of the boundary by a circle. -/
def HasSmoothBoundary (K : Set Plane) : Prop :=
  ∃ γ : ℝ → Plane,
    ContDiff ℝ ∞ γ ∧ Function.Periodic γ 1 ∧ Set.InjOn γ (Set.Ico 0 1) ∧
      (∀ t, deriv γ t ≠ 0) ∧ Set.range γ = frontier K

/-- An infinite specular trajectory from the origin in direction v. -/
def IsTrapped {n : ℕ} (mirror : Fin n → Set Plane) (v : Plane) : Prop :=
  ∃ (point direction : ℕ → Plane) (hit : ℕ → Fin n) (length : ℕ → ℝ),
    point 0 = 0 ∧ direction 0 = v ∧
      ∀ k : ℕ,
        0 < length k ∧ (k ≠ 0 → hit k ≠ hit (k - 1)) ∧
        point (k + 1) = point k + length k • direction k ∧
        point (k + 1) ∈ frontier (mirror (hit k)) ∧
        (∀ (i : Fin n) (t : ℝ), (k = 0 ∨ i ≠ hit (k - 1)) →
          0 < t → t < length k → point k + t • direction k ∉ mirror i) ∧
        ∃ normal : Plane,
          ‖normal‖ = 1 ∧
          (∀ y ∈ mirror (hit k), inner ℝ normal (y - point (k + 1)) ≤ 0) ∧
          direction (k + 1) = direction k - (2 * inner ℝ (direction k) normal) • normal

/-- Can finitely many disjoint smooth convex mirrors trap all rays from a
single point source in the plane? -/
theorem main :
    ∃ (n : ℕ) (mirror : Fin n → Set Plane),
      (∀ i, IsCompact (mirror i) ∧ Convex ℝ (mirror i) ∧
        (interior (mirror i)).Nonempty ∧ HasSmoothBoundary (mirror i) ∧
        0 ∉ mirror i) ∧
      (∀ i j, i ≠ j → Disjoint (mirror i) (mirror j)) ∧
      ∀ v : Plane, ‖v‖ = 1 → IsTrapped mirror v := by
  sorry

end OMA.S_mo_156344
