import Mathlib

/-!
# Can the optimal packing density in the integer lattice be irrational?

Source: https://mathoverflow.net/questions/454946
Credit: @jpollard-cs
-/

namespace OMA.S_mo_454946

/-- The translate of a finite shape by a lattice vector. -/
def translate {d : ℕ} (a : Fin d → ℤ) (S : Finset (Fin d → ℤ)) :
    Set (Fin d → ℤ) :=
  {x | ∃ s ∈ S, x = a + s}

/-- Lower asymptotic density in centered integer cubes of side length 2n + 1. -/
noncomputable def lowerDensity {d : ℕ} (U : Set (Fin d → ℤ)) : ℝ :=
  Filter.liminf (fun n : ℕ =>
    (((U ∩ {x | ∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ (n : ℤ)}).ncard : ℝ) /
      (2 * (n : ℝ) + 1) ^ d)) Filter.atTop

/-- The supremum of the covered lower densities over disjoint translates. -/
noncomputable def packingDensity {d : ℕ} (S : Finset (Fin d → ℤ)) : ℝ :=
  sSup {r : ℝ | ∃ A : Set (Fin d → ℤ),
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Disjoint (translate a S) (translate b S)) ∧
    r = lowerDensity {x | ∃ a ∈ A, x ∈ translate a S}}

theorem main : ∃ d : ℕ, 0 < d ∧ ∃ S : Finset (Fin d → ℤ),
    Irrational (packingDensity S) := by
  sorry

end OMA.S_mo_454946
