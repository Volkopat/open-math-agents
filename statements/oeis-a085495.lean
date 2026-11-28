import Mathlib

/-!
# OEIS A085495: finite subgroups of `GL(n, ℚ)` versus `SL(n, ℚ)`

Source: https://oeis.org/A085495
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the maximal order of a finite subgroup of `GL(n, ℚ)`. Conjecture (Song, 2021):
`a(n)/2` is the maximal order of a finite subgroup of `SL(n, ℚ)`.

Conventions:
* `n ≥ 1`. The maximal orders exist (finite subgroups of `GL(n, ℚ)` have bounded order, by
  Minkowski); they are written as `sSup` of the orders `Nat.card H` of finite subgroups `H`.
  `main` states `2 · max_SL = max_GL`.
-/

namespace OMA.S_oeis_a085495

/-- Maximal order of a finite subgroup of `GL(n, ℚ)`. -/
noncomputable def maxGL (n : ℕ) : ℕ :=
  sSup {k | ∃ H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ), Finite H ∧ Nat.card H = k}

/-- Maximal order of a finite subgroup of `SL(n, ℚ)`. -/
noncomputable def maxSL (n : ℕ) : ℕ :=
  sSup {k | ∃ H : Subgroup (Matrix.SpecialLinearGroup (Fin n) ℚ), Finite H ∧ Nat.card H = k}

/-- `a(n)/2` is the maximal order of a finite subgroup of `SL(n, ℚ)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 2 * maxSL n = maxGL n := by
  sorry

end OMA.S_oeis_a085495
