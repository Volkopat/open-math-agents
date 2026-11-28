import Mathlib

/-!
# A090691: 5x - 1 sequence starting at 50 (a(n+1) = a(n)/2 if a(n) is even, or 5*a(n)-1 if a(n) is odd).

Source: https://oeis.org/A090691
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

There is a general conjecture (see, e.g., the paper of Heppner, Eine Bemerkung zum
Hasse-Syracuse-Algorithmus, Arch. Math. (Basel) 31 (1978/79), 317-320) that for the
5x-1 problem there are divergent sequences.
-/

namespace OMA.S_oeis_a090691

def step (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else 5 * x - 1

theorem main :
    ∃ x : ℕ, 1 ≤ x ∧ Filter.Tendsto (fun n => step^[n] x) Filter.atTop Filter.atTop := by
  sorry

end OMA.S_oeis_a090691
