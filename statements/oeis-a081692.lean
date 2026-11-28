import Mathlib

/-!
# A081692: Complementary mex sequence A_n with B_n = B_{n-1} + (A_n - A_{n-1})(A_n - A_{n-1} + 1)

Source: https://oeis.org/A081692
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Define two sequences by A_n = mex{A_i, B_i : 0 <= i < n},
B_n = B_{n-1} + (A_n - A_{n-1})(A_n - A_{n-1} + 1), starting with A_0 = B_0 = 0.
Conjecture: Except for the initial 0, A_n is the sequence of positions of 0 in the
fixed point of the morphism 0 -> 01, 1 -> 0000.
-/

namespace OMA.S_oeis_a081692

noncomputable def abPrefix : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 0)]
  | n + 1 =>
    let prev := abPrefix n
    let last := prev.getLastD (0, 0)
    let used : Finset ℕ := (prev.map Prod.fst ++ prev.map Prod.snd).toFinset
    let an := sInf {x : ℕ | x ∉ used}
    let d := an - last.1
    let bn := last.2 + d * (d + 1)
    prev ++ [(an, bn)]

noncomputable def aSeq (n : ℕ) : ℕ :=
  ((abPrefix n).getLastD (0, 0)).1

def morphStep (w : List Bool) : List Bool :=
  w.flatMap fun b => if b then [false, false, false, false] else [false, true]

def fixedWord (k : ℕ) : Bool :=
  (morphStep^[k + 1] [false]).getD k false

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      aSeq n = Nat.nth (fun m => 1 ≤ m ∧ fixedWord (m - 1) = false) (n - 1) := by
  sorry

end OMA.S_oeis_a081692
