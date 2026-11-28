import Mathlib

/-!
A087200: a(n) is the smallest m such that m > A005235(n) and A002110(n)+m is prime.

Source: https://oeis.org/A087200
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) is the second m (first m is A005235(n)) such that m > 1 and A002110(n)+m is prime.
Conjecture: every term of this sequence is prime.
-/

namespace OMA.S_oeis_a087200

noncomputable def primorial (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

noncomputable def firstM (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ (primorial n + m).Prime}

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | firstM n < m ∧ (primorial n + m).Prime}

theorem main : ∀ n : ℕ, 1 ≤ n → (a n).Prime := by
  sorry

end OMA.S_oeis_a087200
