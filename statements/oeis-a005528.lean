import Mathlib

/-!
# OEIS A005528 (Størmer numbers): asymptotic density conjecture

Source: https://oeis.org/A005528
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A005528 lists the Størmer numbers: positive integers `k` such that the largest prime factor of
`k² + 1` is at least `2k`. Everest and Harman conjecture (as recorded in the entry) that
`a(n) ~ c n` with `c = 1/log 2`.

Encoding: `a(n)` is the `n`-th such number, `n ≥ 1` (`Nat.nth` is 0-indexed).
-/

namespace OMA.S_oeis_a005528

open Filter

/-- Largest prime factor of `k² + 1` is at least `2k`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ ∃ p : ℕ, p.Prime ∧ p ∣ k ^ 2 + 1 ∧ 2 * k ≤ p

/-- `a(n)`, the `n`-th term (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Everest–Harman conjecture. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (nhds (1 / Real.log 2)) := by
  sorry

end OMA.S_oeis_a005528
