import Mathlib

/-!
# OEIS A057566: collinear triples in a 3 × n grid

Source: https://oeis.org/A057566
`a n` is the number of collinear triples of points in a `3 × n` rectangular grid of lattice
points. Conjecture (fits all listed terms):
`a(n) = 5 ⌊(2n³ - 3n² - 2n + 3)/24⌋ + ⌊(2(n-1)³ - 3(n-1)² - 2(n-1) + 3)/24⌋ + n`.

Conventions. The grid is `Fin 3 × Fin n` viewed in `ℤ²`; a collinear triple is a
3-element set of grid points lying on a line (zero cross product). `n ≥ 1`; floors are
integer division (the numerators are nonnegative for `n ≥ 1`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a057566

/-- Three lattice points are collinear. -/
def Collinear3 (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) = 0

/-- Collinear 3-subsets of the `3 × n` grid. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {S : Finset (Fin 3 × Fin n) | S.card = 3 ∧
    ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
      Collinear3 ((p.1 : ℤ), (p.2 : ℤ)) ((q.1 : ℤ), (q.2 : ℤ)) ((r.1 : ℤ), (r.2 : ℤ))}

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = 5 * ((2 * n ^ 3 - 3 * n ^ 2 - 2 * n + 3 : ℤ) / 24) +
        ((2 * (n - 1) ^ 3 - 3 * (n - 1) ^ 2 - 2 * (n - 1) + 3 : ℤ) / 24) + n := by
  sorry

end OMA.S_oeis_a057566
