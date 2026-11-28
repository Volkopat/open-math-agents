import Mathlib

/-!
# Maximum probability that i.i.d. random vectors in `𝔽₂ⁿ` are linearly independent

Source: https://mathoverflow.net/questions/380970
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 380970, Jan 2021): `m` vectors of `𝔽₂ⁿ` are selected independently
according to a distribution `P` on `𝔽₂ⁿ` (equivalently, the rows of an `m × n` matrix are sampled
independently from `P`). For which `P` is the probability that they are linearly independent
(the matrix has full rank) maximized? "It seems obvious that, for any `m ∈ {2, …, n}`, the maximum
is attained when `P` is uniform over all the non-zero vectors"; this is known for `m = 2`. The asker
confirms in a comment that selecting a vector twice counts as linear dependence (the selections
form an indexed family). This file states the conjectured answer.

Modelling choices:
* `𝔽₂ⁿ` is `Fin n → ZMod 2`. A distribution on it is a weight function `p` with nonnegative values
  summing to `1`.
* The `m` selections form a family `v : Fin m → 𝔽₂ⁿ` with probability `∏ i, p (v i)`, and the
  event is `LinearIndependent (ZMod 2) v` (so a repeated vector is a failure).
* "The maximum is attained at the uniform distribution on non-zero vectors" is stated as: the
  probability for any `p` is at most the probability for that uniform distribution.
-/

namespace OMA.S_mo_380970

open Classical

/-- The probability that `m` independent samples from the weights `p` on `𝔽₂ⁿ` are linearly
independent. -/
noncomputable def probIndep (n m : ℕ) (p : (Fin n → ZMod 2) → ℝ) : ℝ :=
  ∑ v : Fin m → (Fin n → ZMod 2),
    (∏ i, p (v i)) * (if LinearIndependent (ZMod 2) v then 1 else 0)

/-- The uniform distribution on the non-zero vectors of `𝔽₂ⁿ`. -/
noncomputable def uniformNonzero (n : ℕ) (x : Fin n → ZMod 2) : ℝ :=
  if x = 0 then 0 else 1 / ((2 : ℝ) ^ n - 1)

/-- **MathOverflow 380970 (conjectured answer).** For `2 ≤ m ≤ n`, the uniform distribution on
the non-zero vectors maximizes the probability that `m` i.i.d. samples are linearly
independent. -/
theorem main :
    ∀ n m : ℕ, 2 ≤ m → m ≤ n →
      ∀ p : (Fin n → ZMod 2) → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
        probIndep n m p ≤ probIndep n m (uniformNonzero n) := by
  sorry

end OMA.S_mo_380970
