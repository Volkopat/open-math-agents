import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a060521

/-- A `3 × n` grid of binary cells with no 3 cells of the same color contiguous
vertically or horizontally. -/
def ValidGrid (n : ℕ) (g : Fin 3 → Fin n → Bool) : Prop :=
  (∀ j : Fin n, ¬ (g 0 j = g 1 j ∧ g 1 j = g 2 j)) ∧
  (∀ i : Fin 3, ∀ j : ℕ, (hj : j + 2 < n) →
    ¬ (g i ⟨j, by omega⟩ = g i ⟨j + 1, by omega⟩ ∧
       g i ⟨j + 1, by omega⟩ = g i ⟨j + 2, by omega⟩))

/-- OEIS A060521: the number of `3 × n` grids of black and white cells with no
3 of the same color vertically or horizontally contiguous. -/
noncomputable def a060521 (n : ℕ) : ℕ :=
  Nat.card {g : Fin 3 → Fin n → Bool // ValidGrid n g}

/-- OEIS A060521 conjecture:
`a(n + 4) = 2 * a(n + 3) + 5 * a(n + 2) - a(n)` for all `n ≥ 1`, written over `ℕ` as
`a(n + 4) + a(n) = 2 * a(n + 3) + 5 * a(n + 2)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a060521 (n + 4) + a060521 n = 2 * a060521 (n + 3) + 5 * a060521 (n + 2) := by
  sorry

end OMA.S_oeis_a060521
