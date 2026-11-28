import FormalConjectures.ErdosProblems.«322»

-- Reduction Erdos322.erdos_322.R1 of Erdős Problem 322
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: split the statement by the exponent k. Different k are unrelated (representations
-- of n as a sum of k k-th powers for one k say nothing about another k), so the split is genuine.
--   H1: k = 3. Known: Mahler (1936) disproved Hypothesis K of Hardy and Littlewood for cubes,
--       constructing infinitely many n with at least a constant times n^(1/12) representations
--       as a sum of three cubes (see erdosproblems.com/322). Not in Mathlib.
--   H2: every k ≥ 4. This is the open part (Erdős believed it; unknown).
-- main: case split on k = 3 or k ≥ 4. No computer search was used.

namespace OMA.R_Erdos322_erdos_322_R1

open Erdos322

def H1 : Prop :=
  ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount 3 n}.Infinite

def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ c > (0 : ℝ),
    {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite

theorem main : H1 → H2 → type_of% @Erdos322.erdos_322 := by
  intro h1 h2 k hk
  rcases (by omega : k = 3 ∨ 4 ≤ k) with rfl | h4
  · simpa [H1] using h1
  · exact h2 k h4

end OMA.R_Erdos322_erdos_322_R1
