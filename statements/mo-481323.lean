import Mathlib

namespace OMA.S_mo_481323

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def unitSquare : Set Plane :=
  {x | ∀ axis : Fin 2, x axis ∈ Set.Icc (0 : ℝ) 1}

def side {n : ℕ} (vertex : Fin n → Plane) (i : Fin n) : Set Plane :=
  segment ℝ (vertex i) (vertex (finRotate n i))

def endpoints {n : ℕ} (vertex : Fin n → Plane) (i : Fin n) : Set Plane :=
  {vertex i, vertex (finRotate n i)}

/-- A simple unit-sided polygon in a closed unit square has odd length
unless its outline is the boundary of the square. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n → ∀ vertex : Fin n → Plane,
      Function.Injective vertex →
      (∀ i, vertex i ∈ unitSquare) →
      (∀ i, dist (vertex i) (vertex (finRotate n i)) = 1) →
      (∀ i j, i ≠ j →
        side vertex i ∩ side vertex j ⊆ endpoints vertex i ∩ endpoints vertex j) →
      (⋃ i, side vertex i) ≠ frontier unitSquare →
      Odd n := by
  sorry

end OMA.S_mo_481323
