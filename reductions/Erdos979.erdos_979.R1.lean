import FormalConjectures.ErdosProblems.«979»

-- Reduction Erdos979.erdos_979.R1 of Erdős Problem 979
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: the target says that for every k ≥ 2 the number of representations
-- n = p_1^k + ... + p_k^k (primes p_i) is unbounded. Different values of k concern
-- unrelated equations, so no case implies another, and we split by k:
--   H1: k = 2 (proved by Erdős 1937, J. London Math. Soc.; not in Mathlib),
--   H2: k = 3 (Erdős, unpublished; a Lean proof is referenced upstream),
--   H3: every k ≥ 4 (the part that is still open).
-- main: case analysis k = 2, k = 3, k ≥ 4. No computer search was used.

namespace OMA.R_Erdos979_erdos_979_R1

open Erdos979

/-- The case k = 2 (Erdős 1937). -/
def H1 : Prop :=
  Filter.limsup (fun n => (solutionSet n 2).encard) Filter.atTop = ⊤

/-- The case k = 3. -/
def H2 : Prop :=
  Filter.limsup (fun n => (solutionSet n 3).encard) Filter.atTop = ⊤

/-- The open part: every k ≥ 4. -/
def H3 : Prop :=
  ∀ k ≥ 4, Filter.limsup (fun n => (solutionSet n k).encard) Filter.atTop = ⊤

theorem main : H1 → H2 → H3 → type_of% @Erdos979.erdos_979 := by
  intro h1 h2 h3 k hk
  rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | h
  · simpa [H1] using h1
  · simpa [H2] using h2
  · exact h3 k h

end OMA.R_Erdos979_erdos_979_R1
