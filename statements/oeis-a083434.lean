import Mathlib

/-!
# A083434: a(n) = smallest palindrome not included earlier and with the same prime signature as n, or 0 if no such palindrome exists.

Source: https://oeis.org/A083434
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: There are infinitely many zeros in this sequence.
-/

namespace OMA.S_oeis_a083434

def isPalindrome (m : ℕ) : Prop :=
  (Nat.digits 10 m).reverse = Nat.digits 10 m

noncomputable def primeSig (n : ℕ) : Multiset ℕ :=
  n.factorization.support.val.map (fun p => n.factorization p)

noncomputable def seqRev : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let prev := seqRev n
    let S := {m : ℕ | 0 < m ∧ isPalindrome m ∧ primeSig m = primeSig (n + 1) ∧ m ∉ prev}
    let next := open Classical in if S.Nonempty then sInf S else 0
    next :: prev

noncomputable def a (n : ℕ) : ℕ :=
  (seqRev n).headD 0

theorem main :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ a n = 0} := by
  sorry

end OMA.S_oeis_a083434
