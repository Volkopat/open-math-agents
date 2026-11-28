import Mathlib

/-!
# A084199: Smallest prime q < prime(n) such that q+1 divides prime(n)+1, a(n) = 1 if no such q exists.

Source: https://oeis.org/A084199
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: A008578 is the range of values (or A000040 = range of values > 1).
-/

namespace OMA.S_oeis_a084199

noncomputable def a (n : ℕ) : ℕ :=
  let p := Nat.nth Nat.Prime n
  let S := {q : ℕ | Nat.Prime q ∧ q < p ∧ (q + 1) ∣ (p + 1)}
  open Classical in if S.Nonempty then sInf S else 1

theorem main :
    ∀ q : ℕ, Nat.Prime q → ∃ n : ℕ, a n = q := by
  sorry

end OMA.S_oeis_a084199
