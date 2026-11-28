import Mathlib

/-!
# The Borodin–Kostochka Conjecture

Source: https://www.openproblemgarden.org/op/the_borodin_kostochka_conjecture
Credit: @lzvxck

The source: every graph with maximum degree `Δ ≥ 9` has chromatic number at most
`max {Δ - 1, ω}`, where `ω` is the clique number.

Graphs are finite and simple. `Δ` is `G.maxDegree`, `ω` is `G.cliqueNum`, and the chromatic
number is Mathlib's `G.chromaticNumber` (valued in `ℕ∞`). Since `Δ ≥ 9`, `Δ - 1` is the usual
difference.
-/

namespace OMA.S_opg_the_borodin_kostochka_conjecture

/-- **Borodin–Kostochka conjecture.** A finite graph with maximum degree `Δ ≥ 9` has
chromatic number at most `max (Δ - 1) ω`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    9 ≤ G.maxDegree →
      G.chromaticNumber ≤ ((max (G.maxDegree - 1) G.cliqueNum : ℕ) : ℕ∞) := by
  sorry

end OMA.S_opg_the_borodin_kostochka_conjecture
