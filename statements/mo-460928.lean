import Mathlib

/-!
# On fifth powers forming a Sidon set

Source: https://mathoverflow.net/questions/460928
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The question calls a set `S` of natural numbers a Sidon set if `a + b = c + d` with
`a, b, c, d ∈ S` implies `{a, b} = {c, d}`. It recalls that Erdős asked whether the set of fifth
powers is a Sidon set, and its second question asks how far computers have checked that
conjecture. The other parts of the question (progress on Ruzsa's result, algorithms, a
reference for Euler's proof) are requests for literature and are not mathematical statements;
the conjecture the question is about is stated below.

Conventions:
* the fifth powers are `{n ^ 5 | n ≥ 1}`; including `0 = 0 ^ 5` would not change the truth of the
  statement, since the only extra equations `0 + a^5 = b^5 + c^5` with `b, c ≥ 1` are excluded by
  Fermat's Last Theorem for exponent `5`;
* for `a + b = c + d`, the set equality `{a, b} = {c, d}` is equivalent to
  `(a = c ∧ b = d) ∨ (a = d ∧ b = c)`, which is the form used in `IsSidon`.
-/

namespace OMA.S_mo_460928

/-- `S` is a Sidon set: all pairwise sums `a + b` (with `a = b` allowed) are distinct, up to
order of the summands. -/
def IsSidon (S : Set ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Erdős's question: the set of (positive) fifth powers is a Sidon set. -/
theorem main : IsSidon {m : ℕ | ∃ n : ℕ, 1 ≤ n ∧ m = n ^ 5} := by
  sorry

end OMA.S_mo_460928
