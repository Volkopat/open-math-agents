import Mathlib

/-!
# A027833: Distances between successive 2's in the sequence of prime gaps

Source: https://oeis.org/A027833
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjectures:
Let twinIdx(n) be the n-th index k (0-indexed) such that prime(k+1) - prime(k) = 2, and let
a(n) = twinIdx(n+1) - twinIdx(n) be the distance between successive 2's in the prime gap
sequence A001223.
1. a(n) < (log(p + 1))^2 where p = prime(twinIdx(n)) (so p + 1 = A014574(n+1)).
2. Every positive integer occurs in the sequence a(n).
-/

namespace OMA.S_oeis_a027833

/-- The n-th index k (0-indexed) where the prime gap p_{k+1} - p_k equals 2. -/
noncomputable def twinIdx (n : ℕ) : ℕ :=
  Nat.nth (fun k => Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k = 2) n

/-- Distance between successive twin-prime indices in the prime sequence. -/
noncomputable def a (n : ℕ) : ℕ :=
  twinIdx (n + 1) - twinIdx n

/-- Conjectures: a(n) < (log(p_{twinIdx n} + 1))^2 for all n, and every d >= 1 appears in a. -/
theorem main :
    (∀ n : ℕ, (a n : ℝ) < (Real.log ((Nat.nth Nat.Prime (twinIdx n) + 1 : ℕ) : ℝ)) ^ 2) ∧
    (∀ d : ℕ, 1 ≤ d → ∃ n : ℕ, a n = d) := by
  sorry

end OMA.S_oeis_a027833
