import FormalConjectures.ErdosProblems.«68»

/-!
# Erdős problem 68: irrationality of a factorial reciprocal series

The pinned module proves the geometric-expansion identity
`sum_factorial_inv_eq_geometric`: the single series over `1 / (n! - 1)` equals a
double geometric series. That identity is an upstream-proved bridge, while the
irrationality of the resulting double series is the genuinely open core.
`main` rewrites the target by the bridge and applies the open hypothesis.
-/

-- Reduction Erdos68.erdos_68.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos68_erdos_68_R1

/-- Open core: irrationality of the geometric double series. -/
def H1 : Prop :=
  Irrational (∑' n : ℕ, ∑' k : ℕ, (1 : ℝ) / ((n + 2).factorial : ℝ) ^ (k + 1))

/-- Upstream-proved bridge: the geometric expansion of `1 / (n! - 1)`. -/
def H2 : Prop :=
  let f (n k : ℕ) : ℝ := 1 / ((n + 2).factorial : ℝ) ^ (k + 1)
  (∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1)) = ∑' n : ℕ, ∑' k : ℕ, f n k

theorem main : H1 → H2 → type_of% @Erdos68.erdos_68 := by
  intro h1 h2
  rw [h2]
  exact h1

end OMA.R_Erdos68_erdos_68_R1
