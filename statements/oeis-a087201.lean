import Mathlib

/-!
# A087201: a(n) is the smallest m such that m > A055211(n) and A002110(n)-m is prime.

Source: https://oeis.org/A087201
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(1) and a(2) are not defined. a(n) is the second m (first m is A055211(n)) such that
m > 1 and A002110(n)-m is prime. Conjecture: every term of this sequence is prime.
-/

namespace OMA.S_oeis_a087201

noncomputable def primorial (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

noncomputable def firstM (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ m < primorial n ∧ (primorial n - m).Prime}

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | firstM n < m ∧ m < primorial n ∧ (primorial n - m).Prime}

theorem main : ∀ n : ℕ, 3 ≤ n → (a n).Prime := by
  sorry

end OMA.S_oeis_a087201
