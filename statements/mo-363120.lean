import Mathlib

namespace OMA.S_mo_363120

abbrev Square (k : ℕ) := Fin (2 * k + 1) × Fin (2 * k + 1)

/-- A step down and left, one step up, or one step right. -/
def Step {k : ℕ} (p q : Square k) : Prop :=
  (q.1.val + 1 = p.1.val ∧ q.2.val + 1 = p.2.val) ∨
  (q.1 = p.1 ∧ q.2.val = p.2.val + 1) ∨
  (q.1.val = p.1.val + 1 ∧ q.2 = p.2)

/-- A player to move can choose a new square from which either the
opponent has no move or every reply leads to another winning position. -/
inductive Winning (k : ℕ) : Square k → Finset (Square k) → Prop
  | step {p q : Square k} {visited : Finset (Square k)}
      (move : Step p q) (fresh : q ∉ visited)
      (afterReply : ∀ r : Square k, Step q r → r ∉ insert q visited →
        Winning k r (insert r (insert q visited))) :
      Winning k p visited

/-- With both starting coordinates even, the second player can force a win. -/
theorem main :
    ∀ (k : ℕ) (start : Square k),
      Even start.1.val → Even start.2.val →
        ∀ first : Square k, Step start first → first ≠ start →
          Winning k first {start, first} := by
  sorry

end OMA.S_mo_363120
