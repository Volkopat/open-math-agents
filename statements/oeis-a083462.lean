import Mathlib

/-!
# A083462: Smallest palindrome k such that k - n is a distinct power of 2; i.e., a power of 2 that has not arisen earlier; or 0 if no such k exists.

Source: https://oeis.org/A083462
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) > 0 for the following values of n: 0, 1, 2, 3, 6, 12, 13, 16, 18, 20, 23, 33, 36, 55, 59, 64, 77, 87, 118, 137, 230, 545, 610, 750, 825. Conjecturally, there are no other such n <= 1000.
-/

namespace OMA.S_oeis_a083462

def isPalindrome (m : ℕ) : Prop :=
  (Nat.digits 10 m).reverse = Nat.digits 10 m

noncomputable def seqRev : ℕ → List (Option (ℕ × ℕ))
  | 0 =>
    let S := {e : ℕ | isPalindrome (2 ^ e)}
    [open Classical in if S.Nonempty then some (2 ^ sInf S, sInf S) else none]
  | n + 1 =>
    let prev := seqRev n
    let S := {e : ℕ | isPalindrome ((n + 1) + 2 ^ e) ∧ ∀ p ∈ prev, p.map Prod.snd ≠ some e}
    let next := open Classical in if S.Nonempty then some ((n + 1) + 2 ^ sInf S, sInf S) else none
    next :: prev

noncomputable def a (n : ℕ) : ℕ :=
  match (seqRev n).headD none with
  | some (k, _) => k
  | none => 0

def knownPositives : Finset ℕ :=
  {0, 1, 2, 3, 6, 12, 13, 16, 18, 20, 23, 33, 36, 55, 59, 64, 77, 87, 118, 137, 230, 545, 610, 750, 825}

theorem main :
    ∀ n : ℕ, n ≤ 1000 → 0 < a n → n ∈ knownPositives := by
  sorry

end OMA.S_oeis_a083462
