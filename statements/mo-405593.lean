import Mathlib

/-!
# MathOverflow 405593: are the Erdős polynomials irreducible?

Source: https://mathoverflow.net/questions/405593
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The question defines the Erdős polynomial `f_n(x) = Sum_{0 ≤ i, j ≤ n} x^(i j)` (named after
OEIS A027424) and asks (Question 1): is `f_n(x)` always irreducible over `ℚ`? It is reported
irreducible for `n ≤ 20`. (Question 2 asks the same for the `k`-fold analogue
`Sum_{0 ≤ i_1, …, i_k ≤ n} x^(i_1 ⋯ i_k)`; it is not stated here.)

We state the affirmative answer to Question 1 (a disproof of `main` answers it negatively).

Conventions: "always" is read as "for every `n ≥ 1`": `f_0 = 1` is a unit and so is not
irreducible for trivial reasons. The double sum counts pairs `(i, j)` with multiplicity, as in
the source's example `f_5 = x^25 + 2x^20 + … + 11`. Irreducibility is `Irreducible` in `ℚ[X]`.
-/

namespace OMA.S_mo_405593

open Polynomial

/-- The Erdős polynomial `f_n(x) = Sum_{0 ≤ i, j ≤ n} x^(i j)` over `ℚ`. -/
noncomputable def erdosPoly (n : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), X ^ (i * j)

/-- For every `n ≥ 1`, `f_n(x)` is irreducible over `ℚ`. -/
theorem main : ∀ n : ℕ, 0 < n → Irreducible (erdosPoly n) := by
  sorry

end OMA.S_mo_405593
