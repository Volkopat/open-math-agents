import Mathlib

/-!
# OEIS A002312 (non-Størmer numbers): asymptotic density conjecture

Source: https://oeis.org/A002312
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A002312 lists the positive integers `k` such that the largest prime factor of `k² + 1` is
less than `2k` (arctangent-reducible / non-Størmer numbers). Everest and Harman conjecture
(as recorded in the entry) that `a(n) ~ c n` with `c = 1/(1 - log 2)`.

Encoding: `a(n)` is the `n`-th such number, `n ≥ 1` (`Nat.nth` is 0-indexed).
-/

namespace OMA.S_oeis_a002312

open Filter

/-- Largest prime factor of `k² + 1` is less than `2k`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ ∀ p : ℕ, p.Prime → p ∣ k ^ 2 + 1 → p < 2 * k

/-- `a(n)`, the `n`-th term (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Everest–Harman conjecture. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (nhds (1 / (1 - Real.log 2))) := by
  sorry

end OMA.S_oeis_a002312
