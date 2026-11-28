import Mathlib

/-!
# OEIS A048799: irrationality of `∑ 1/S(n)!` (Kempner numbers)

Source: https://oeis.org/A048799
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A048799 is the decimal expansion of `∑_{n ≥ 2} 1/S(n)!`, where `S(n)` (A002034) is the Kempner
number, the least `m` with `n ∣ m!`. Conjecture (Bhattacharya, 2008): this constant is irrational
(the same is conjectured for six related constants in other entries).

Conventions:
* `S(n) = sInf {m | n ∣ m!}`; the series converges (the `n` with `S(n) = m` are divisors of `m!`,
  and `∑ d(m!)/m!` converges), and is a `tsum` over `n ≥ 2`.
-/

namespace OMA.S_oeis_a048799

/-- The Kempner number `S(n)`. -/
noncomputable def S (n : ℕ) : ℕ := sInf {m : ℕ | n ∣ m.factorial}

/-- `∑_{n ≥ 2} 1/S(n)!` is irrational. -/
theorem main : Irrational (∑' n : ℕ, 1 / ((S (n + 2)).factorial : ℝ)) := by
  sorry

end OMA.S_oeis_a048799
