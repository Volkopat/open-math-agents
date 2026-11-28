import Mathlib

/-!
# OEIS A087324: numbers with the same prime signature as their 9's complement

Source: https://oeis.org/A087324
Numbers `n` such that `n` and its 9's complement have the same prime signature. Conjectures:
(1) the sequence is infinite; (2) for every prime signature there is a term with that
signature. `main` is their conjunction.

Conventions. The 9's complement of a `d`-digit number `n` is `10^d - 1 - n`. The prime
signature of `m ≥ 1` is the multiset of exponents in its factorisation; a prime signature is
any finite multiset of positive integers (the empty one belongs to `1`). Terms are taken
`≥ 1` with positive 9's complement.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a087324

/-- The prime signature of `m`. -/
noncomputable def sig (m : ℕ) : Multiset ℕ := m.primeFactors.val.map m.factorization

/-- The 9's complement of `n`. -/
def comp9 (n : ℕ) : ℕ := 10 ^ (Nat.digits 10 n).length - 1 - n

/-- `n` is a term. -/
def P (n : ℕ) : Prop := 1 ≤ n ∧ 1 ≤ comp9 n ∧ sig n = sig (comp9 n)

theorem main :
    {n : ℕ | P n}.Infinite ∧
      ∀ s : Multiset ℕ, (∀ e ∈ s, 1 ≤ e) → ∃ n : ℕ, P n ∧ sig n = s := by
  sorry

end OMA.S_oeis_a087324
