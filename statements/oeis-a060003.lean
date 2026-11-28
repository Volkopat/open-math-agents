import Mathlib

/-!
# OEIS A060003: odd numbers not of the form `p + 2k²`

Source: https://oeis.org/A060003
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A060003 lists the odd numbers that are not `p + 2k²` with `p` prime and `k > 0`:
`1, 3, 17, 137, 227, 977, 1187, 1493, 5777, 5993`. The entry records Goldbach's (false) conjecture
that every odd composite has such a form, with `5777` and `5993` the only known exceptions, and
that any further term exceeds `10⁹`; the conjecture behind the entry is that the list is complete.
`main` states that these ten numbers are the only odd numbers not of the form `p + 2k²`.
-/

namespace OMA.S_oeis_a060003

/-- `n = p + 2k²` with `p` prime and `k ≥ 1`. -/
def Rep (n : ℕ) : Prop := ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + 2 * k ^ 2

/-- The complete list of exceptions. -/
theorem main : {n : ℕ | Odd n ∧ ¬ Rep n} = {1, 3, 17, 137, 227, 977, 1187, 1493, 5777, 5993} := by
  sorry

end OMA.S_oeis_a060003
