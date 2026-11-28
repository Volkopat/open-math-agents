import FormalConjectures.ErdosProblems.«5»

open Filter
open scoped Topology

-- Reduction Erdos5.erdos_5.R1 of Erdős Problem 5
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 5: limit points of normalized prime gaps

The target asks that every nonnegative real `C` is the limit of the normalized prime gaps
along a strictly increasing sequence of indices. The pinned module proves the bridge
`Erdos5.mem_limitPointSet_iff`: membership in `Erdos5.limitPointSet` is *by definition* the
existence of such a subsequence. The reduction separates the genuinely open analytic content
(the limit-point set contains all of `Ici 0`) from that proved reformulation.
-/

namespace OMA.R_Erdos5_erdos_5_R1

/-- Open core: every nonnegative real is a limit point of the normalized prime gaps. -/
def H1 : Prop :=
  ∀ C : ℝ, 0 ≤ C → C ∈ Erdos5.limitPointSet

/-- Proved bridge (`Erdos5.mem_limitPointSet_iff`): membership in the limit-point set is
    exactly the existence of a strictly monotone subsequence converging to that point. -/
def H2 : Prop :=
  ∀ x : ℝ, x ∈ Erdos5.limitPointSet →
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => Erdos5.normalizedGap (n i)) atTop (𝓝 x)

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5 := by
  intro h1 h2 C hC
  exact h2 C (h1 C hC)

end OMA.R_Erdos5_erdos_5_R1
