import Mathlib

/-!
# A077214: a(1) = 1. a(n+1) is the smallest number which is greater than a(n), coprime to it and has a different prime signature.

Source: https://oeis.org/A077214
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: a(n+1) - a(n) is unbounded.
-/

namespace OMA.S_oeis_a077214

/-- The prime signature of `n` as the multiset of exponents in its prime factorization. -/
noncomputable def primeSignature (n : ℕ) : Multiset ℕ :=
  n.primeFactors.val.map (fun p => n.factorization p)

/-- The next term after `x` in A077214. -/
noncomputable def nextTerm (x : ℕ) : ℕ :=
  sInf { y : ℕ | x < y ∧ Nat.Coprime x y ∧ primeSignature y ≠ primeSignature x }

/-- The `n`-th term of A077214 (0-indexed, with `a 0 = 1`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.iterate nextTerm n 1

theorem main :
    ∀ M : ℕ, ∃ n : ℕ, M < a (n + 1) - a n := by sorry

end OMA.S_oeis_a077214
