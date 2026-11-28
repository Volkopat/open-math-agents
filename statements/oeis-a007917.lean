import Mathlib

/-!
# OEIS A007917: largest prime `≤ n` via a log-sum-exp of totients

Source: https://oeis.org/A007917
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the largest prime `≤ n` (`n ≥ 2`). Conjecture (OEIS entry):
`a(n) = ⌊log (∑_{k=2}^{n} exp(φ(k) + 1))⌋`.

Conventions:
* `n ≥ 2`; `φ` is `Nat.totient`; `log` is the natural logarithm.
-/

namespace OMA.S_oeis_a007917

/-- The largest prime `≤ n` (for `n ≥ 2`). -/
noncomputable def a (n : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ≤ n}

/-- `a(n) = ⌊log ∑_{k=2}^{n} exp(φ(k)+1)⌋` for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (a n : ℤ) = ⌊Real.log (∑ k ∈ Finset.Icc 2 n, Real.exp ((Nat.totient k : ℝ) + 1))⌋ := by
  sorry

end OMA.S_oeis_a007917
