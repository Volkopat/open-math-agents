import FormalConjectures.ErdosProblems.«373»

-- Reduction Erdos373.erdos_373.variants.maximal_solution.R1 of Erdős Problem 373 — maximal solution
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a conjunction: one concrete solution belongs to S, and no solution of S has a
-- larger first coordinate. The two halves are independent: the first is a finite check on
-- 16! = 14! * 5! * 2!, the second is Hickerson's conjecture itself.

namespace OMA.R_Erdos373_erdos_373_variants_maximal_solution_R1

open Erdos373

/-- The concrete identity `16! = 14! * 5! * 2!` with its side conditions: this is the solution
Hickerson conjectures to be the largest. -/
def H1 : Prop := (16, [14, 5, 2]) ∈ Erdos373.S

/-- Hickerson's conjecture proper: every solution of `n! = a₁! ··· aₖ!` with `a₁ ≥ … ≥ aₖ` and
`n - 1 > a₁` has `n ≤ 16`. -/
def H2 : Prop := ∀ s ∈ Erdos373.S, s.fst ≤ 16

theorem main : H1 → H2 → type_of% @Erdos373.erdos_373.variants.maximal_solution := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos373_erdos_373_variants_maximal_solution_R1
