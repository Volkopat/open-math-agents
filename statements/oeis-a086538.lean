import Mathlib

/-!
A086538: n-th partial sum of A086537.

Source: https://oeis.org/A086538
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Every term has a unique prime signature. Conjecture: Every prime signature occurs in the sequence.
-/

namespace OMA.S_oeis_a086538

noncomputable def primeSignature (n : ℕ) : Multiset ℕ :=
  n.factorization.support.val.map n.factorization

noncomputable def seqPair : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 =>
    let prevSum := (seqPair n).2
    let nextA := sInf {m : ℕ | 1 ≤ m ∧
      (∀ i : Fin (n + 1), (seqPair i.val).1 ≠ m) ∧
      (∀ i : Fin (n + 1), primeSignature (prevSum + m) ≠ primeSignature (seqPair i.val).2)}
    (nextA, prevSum + nextA)

noncomputable def partialSum (n : ℕ) : ℕ := (seqPair n).2

theorem main :
    ∀ s : Multiset ℕ, (∀ e ∈ s, 1 ≤ e) → ∃ n : ℕ, primeSignature (partialSum n) = s := by
  sorry

end OMA.S_oeis_a086538
