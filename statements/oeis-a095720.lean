import Mathlib

/-!
# A095720: a(1)=1 and, for n>1, a(n)=a(n-1)+Floor(3n/4) if n is even, else smallest positive integer not yet appeared.

Source: https://oeis.org/A095720
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture. For even n, the ratio a(n)/a(n-1) is asymptotic to 2 as n becomes large.
(At n=3000, the ratio is 2.0004446.)
-/

namespace OMA.S_oeis_a095720

/-- Prefix list of the first `n` terms of A095720. -/
noncomputable def prefixList : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let prev := prefixList (n + 1)
    let nxt :=
      if Even (n + 2) then prev.getLastD 0 + (3 * (n + 2)) / 4
      else sInf {m : ℕ | 1 ≤ m ∧ m ∉ prev}
    prev ++ [nxt]

/-- The `n`-th term of A095720 (1-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  (prefixList n).getLastD 0

theorem main :
    Filter.Tendsto (fun k : ℕ => (a (2 * k + 2) : ℝ) / (a (2 * k + 1) : ℝ))
      Filter.atTop (nhds 2) := by
  sorry

end OMA.S_oeis_a095720
