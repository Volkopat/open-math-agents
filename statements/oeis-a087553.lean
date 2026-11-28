import Mathlib

/-!
# A087553: Squares in which neighboring digits differ at most by 1 (mod 10)

Source: https://oeis.org/A087553
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Squares in which the neighboring decimal digits differ at most by 1, where
neighbors of 1 are 0 and 2, and neighbors of 0 are 1 and 9. The sequence is
infinite with trivial terms 10^(2k) and 9*10^(2k). Conjecture: There are
infinitely many nontrivial terms.
-/

namespace OMA.S_oeis_a087553

/-- Two decimal digits `a` and `b` are adjacent on the 10-cycle (differ by at most 1 mod 10). -/
def digitNeighbors (a b : ℕ) : Prop :=
  (a ≤ b + 1 ∧ b ≤ a + 1) ∨ (a = 0 ∧ b = 9) ∨ (a = 9 ∧ b = 0)

/-- All consecutive decimal digits of `n` are cyclic neighbors. -/
def HasNeighborDigits (n : ℕ) : Prop :=
  let ds := Nat.digits 10 n
  ∀ i : ℕ, (h : i + 1 < ds.length) →
    digitNeighbors (ds[i]'(Nat.lt_of_succ_lt h)) (ds[i + 1]'h)

/-- A term is trivial if it is `10^(2k)` or `9 * 10^(2k)` for some `k`. -/
def IsTrivialTerm (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 10 ^ (2 * k) ∨ n = 9 * 10 ^ (2 * k)

theorem main :
    Set.Infinite {n : ℕ | IsSquare n ∧ HasNeighborDigits n ∧ ¬ IsTrivialTerm n} := by
  sorry

end OMA.S_oeis_a087553
