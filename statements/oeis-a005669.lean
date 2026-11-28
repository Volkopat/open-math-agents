import Mathlib

/-!
# A005669: Asymptotics of indices of record prime gaps

Source: https://oeis.org/A005669
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A005669: Indices of primes where largest gap occurs.

Statement:
Conjecture: log a(n) ~ n/2.

Conventions:
- `Nat.nth Nat.Prime k` is the `k`-th prime (0-indexed: `p_0 = 2, p_1 = 3, ...`).
- `IsRecordGap k` holds when `p_{k+1} - p_k` is strictly larger than all earlier gaps.
- `a(n)` is the 1-indexed prime index of the `n`-th record prime gap.
-/

namespace OMA.S_oeis_a005669

/-- The `k`-th prime gap `p_{k+1} - p_k` (0-indexed). -/
noncomputable def primeGap (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k

/-- `k` is the index of a strictly record-breaking prime gap. -/
def IsRecordGap (k : ℕ) : Prop :=
  ∀ j < k, primeGap j < primeGap k

/-- The 1-indexed prime index of the `n`-th record prime gap (`A005669`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth IsRecordGap n + 1

theorem main :
    Filter.Tendsto (fun n : ℕ => Real.log (a n : ℝ) / ((n : ℝ) / 2))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a005669
