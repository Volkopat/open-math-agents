import Mathlib

/-!
# A083756: Beginning with 5, rearrangement of odd primes such that every concatenation beginning with the first term is a prime.

Source: https://oeis.org/A083756
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: every odd prime is a member.
-/

namespace OMA.S_oeis_a083756

def concat10 (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

def concatList (L : List ℕ) : ℕ :=
  L.foldl concat10 0

noncomputable def seqRev : ℕ → List ℕ
  | 0 => [5]
  | n + 1 =>
    let prev := seqRev n
    let pref := concatList prev.reverse
    let next := sInf {p : ℕ | Nat.Prime p ∧ Odd p ∧ p ∉ prev ∧ Nat.Prime (concat10 pref p)}
    next :: prev

noncomputable def a (n : ℕ) : ℕ :=
  (seqRev n).headD 5

theorem main :
    ∀ p : ℕ, Nat.Prime p → Odd p → ∃ n : ℕ, a n = p := by
  sorry

end OMA.S_oeis_a083756
