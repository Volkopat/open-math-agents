import Mathlib

/-!
# A094340: a(n) = n-th partial sum of A094339 divided by A094339(n+1).

Source: https://oeis.org/A094340
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Every natural number occurs in this sequence.
-/

namespace OMA.S_oeis_a094340

/-- Prefix list of the first `n` terms of A094339. -/
noncomputable def prefixA094339 : ℕ → List ℕ
  | 0 => []
  | 1 => [2]
  | n + 2 =>
    let prev := prefixA094339 (n + 1)
    let nxt := sInf {m : ℕ | 1 ≤ m ∧ m ∉ prev ∧ m ∣ prev.sum}
    prev ++ [nxt]

/-- The `n`-th term of A094339 (1-indexed). -/
noncomputable def a094339 (n : ℕ) : ℕ :=
  (prefixA094339 n).getLastD 0

/-- The `n`-th term of A094340 (1-indexed): `n`-th partial sum of A094339 divided by `A094339(n+1)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (prefixA094339 n).sum / a094339 (n + 1)

theorem main :
    ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a094340
