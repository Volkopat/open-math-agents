import Mathlib

/-!
# Minimal couplings: the least possible mass on the diagonal

Source: https://mathoverflow.net/questions/341790
Credit: @koolkao

Question (pre-kidney, MathOverflow 341790, 2019; CC BY-SA 4.0). A coupling of probability
measures `μ`, `ν` on a common space `Ω` is a probability measure `π` on `Ω²` with marginals `μ`
and `ν`. Every coupling satisfies `π(Δ) ≤ 1 - ‖μ - ν‖_TV`, with equality for a maximal coupling.
Is there a non-trivial lower bound on `π(Δ)`? If singletons are measurable, then
`π({(x, x)}) ≥ (μ({x}) + ν({x}) - 1)₊`, from which one gets a lower bound on `π(Δ)` in the
completely atomic case. Is this bound optimal?

We state the last question for probability measures on a finite set: `main` states that the
least value of `π(Δ)` over all couplings is `∑ₓ (μ({x}) + ν({x}) - 1)₊`. A disproof is a pair
`μ`, `ν` for which every coupling puts more mass than this on the diagonal.

Translation choices:
* `Ω` is `Fin n` for some `n`, with all subsets measurable, so a probability measure is a vector
  `μ : Fin n → ℝ` of nonnegative weights with sum `1`, and a coupling is a nonnegative matrix
  `π : Fin n → Fin n → ℝ` with row sums `μ` and column sums `ν`; its total mass is then
  automatically `1`;
* `π(Δ)` is `∑ₓ π x x`, and `(t)₊` is `max t 0`;
* "the bound is optimal" is `IsLeast`: the bound is attained by some coupling (and it is a lower
  bound for every coupling, as the question notes).
-/

namespace OMA.S_mo_341790

/-- The diagonal masses `∑ₓ π x x` of all couplings `π` of `μ` and `ν`. -/
def diagonalMasses {n : ℕ} (μ ν : Fin n → ℝ) : Set ℝ :=
  {d | ∃ π : Fin n → Fin n → ℝ, (∀ x y, 0 ≤ π x y) ∧ (∀ x, ∑ y, π x y = μ x) ∧
    (∀ y, ∑ x, π x y = ν y) ∧ d = ∑ x, π x x}

/-- For probability vectors `μ`, `ν` on a finite set, the least mass that a coupling puts on the
diagonal is `∑ₓ (μ x + ν x - 1)₊`. -/
theorem main :
    ∀ (n : ℕ) (μ ν : Fin n → ℝ), (∀ x, 0 ≤ μ x) → (∀ x, 0 ≤ ν x) → ∑ x, μ x = 1 →
      ∑ x, ν x = 1 → IsLeast (diagonalMasses μ ν) (∑ x, max (μ x + ν x - 1) 0) := by
  sorry

end OMA.S_mo_341790
