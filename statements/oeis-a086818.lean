import Mathlib

/-!
# A086818: a(1) = 111, a(n) = the smallest squarefree number > a(n-1) which contains all the digits of a(n-1).

Source: https://oeis.org/A086818
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Terms contain exactly three 1's digits and the rest 0's digits.
-/

namespace OMA.S_oeis_a086818

noncomputable def a : ℕ → ℕ
  | 0 => 111
  | n + 1 =>
    sInf {m : ℕ | a n < m ∧ Squarefree m ∧
      (Nat.digits 10 (a n) : Multiset ℕ) ≤ (Nat.digits 10 m : Multiset ℕ)}

theorem main :
    ∀ n : ℕ,
      (Nat.digits 10 (a n)).count 1 = 3 ∧
      ∀ d ∈ Nat.digits 10 (a n), d = 0 ∨ d = 1 := by
  sorry

end OMA.S_oeis_a086818
