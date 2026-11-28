import Mathlib

/-!
# A085135: Numbers whose cyclic permutations are all 7-smooth (A002473).

Source: https://oeis.org/A085135
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Sequence is infinite with trivial terms of the form k*10^r, k = 1 to 9.
Conjecture: There are finitely many nontrivial terms (not of the form k*10^r).
-/

namespace OMA.S_oeis_a085135

def Is7Smooth (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 7

def AllCyclicPermutations7Smooth (n : ℕ) : Prop :=
  let d := Nat.digits 10 n
  ∀ i : ℕ, Is7Smooth (Nat.ofDigits 10 (d.rotate i))

def IsTrivialTerm (n : ℕ) : Prop :=
  ∃ k r : ℕ, 1 ≤ k ∧ k ≤ 9 ∧ n = k * 10 ^ r

theorem main :
    {n : ℕ | 0 < n ∧ AllCyclicPermutations7Smooth n ∧ ¬ IsTrivialTerm n}.Finite := by
  sorry

end OMA.S_oeis_a085135
