import FormalConjectures.ErdosProblems.«572»

-- Reduction Erdos572.erdos_572.R1 of Erdős Problem 572
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 572: the known cases `k = 3, 5` and the open part

The claim is `ex(n; C_{2k}) ≫ n^{1 + 1/k}` for every `k ≥ 3`. No implication runs between
different `k`, so the cases split cleanly:

* `H1` (`k = 3`): `ex(n; C₆) ≫ n^{4/3}`. Known (Benson 1966, Singleton): incidence graphs of
  generalized quadrangles over `𝔽_q` have girth 8; with prime gaps this gives all `n`.
  A known theorem not yet in Mathlib.
* `H2` (`k = 5`): `ex(n; C₁₀) ≫ n^{6/5}`. Known (Benson 1966): incidence graphs of generalized
  hexagons have girth 12. A known theorem not yet in Mathlib.
* `H3` (`k = 4` or `k ≥ 6`): the open part (for `k = 4`, i.e. `C₈`, the best exponent known is
  below `5/4`; Lazebnik–Ustimenko–Woldar give `n^{1 + 2/(3k - 3 + ε)}` in general).
-/

namespace OMA.R_Erdos572_erdos_572_R1

open Filter

/-- `k = 3`: Benson's generalized quadrangle graphs. -/
def H1 : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,
    c * (n : ℝ) ^ (1 + 1 / (3 : ℝ)) ≤
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 3)) : ℝ)

/-- `k = 5`: Benson's generalized hexagon graphs. -/
def H2 : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,
    c * (n : ℝ) ^ (1 + 1 / (5 : ℝ)) ≤
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 5)) : ℝ)

/-- `k = 4` or `k ≥ 6`: open. -/
def H3 : Prop :=
  ∀ k : ℕ, (k = 4 ∨ 6 ≤ k) → ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,
    c * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * k)) : ℝ)

theorem main : H1 → H2 → H3 → type_of% @Erdos572.erdos_572 := by
  intro h1 h2 h3 k hk
  by_cases hk3 : k = 3
  · subst hk3
    simpa [H1] using h1
  by_cases hk5 : k = 5
  · subst hk5
    simpa [H2] using h2
  exact h3 k (by omega)

end OMA.R_Erdos572_erdos_572_R1
