import Mathlib

/-!
# A020498: Greedy admissible sequence

Source: https://oeis.org/A020498
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Define `a(0) = 0`, and for `n ≥ 0`, let `a(n + 1)` be the least integer strictly greater than
`a(n)` such that `{a(0), ..., a(n + 1)}` does not cover all residue classes modulo any prime `p`.
Conjecturally, for every `n`, there are infinitely many `x : ℕ` such that
`x + a(0), x + a(1), ..., x + a(n)` are all prime.

Conventions:
- `IsAdmissible s` holds iff for every prime `p`, there is a residue class in `ZMod p`
  not hit by `s`.
- `IsGreedySeq a` characterizes the unique sequence `a` starting at `a 0 = 0` constructed
  greedily to maintain admissibility.
-/

namespace OMA.S_oeis_a020498

def IsAdmissible (s : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∃ r : ZMod p, ∀ x ∈ s, (x : ZMod p) ≠ r

def IsGreedySeq (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧
  ∀ n : ℕ,
    a (n + 1) > a n ∧
    IsAdmissible ((Finset.range (n + 2)).image a) ∧
    ∀ m : ℕ, a n < m → m < a (n + 1) →
      ¬ IsAdmissible (insert m ((Finset.range (n + 1)).image a))

theorem main :
    ∀ a : ℕ → ℕ, IsGreedySeq a →
      ∀ n : ℕ, Set.Infinite {x : ℕ | ∀ i ≤ n, Nat.Prime (x + a i)} := by
  sorry

end OMA.S_oeis_a020498
