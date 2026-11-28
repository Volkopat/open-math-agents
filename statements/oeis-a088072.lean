import Mathlib

/-!
# A088072: Numbers sandwiched between two prime powers, at least one composite

Source: https://oeis.org/A088072
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Numbers n >= 2 sandwiched between two numbers n - 1 and n + 1 each having only
one distinct prime divisor (i.e., prime powers), at least one of which is composite.
Conjecture (1): The sequence is infinite.
Conjecture (2): There are only finitely many terms sandwiched between two
composite prime powers.
-/

namespace OMA.S_oeis_a088072

/-- `n` is in A088072 if `n ≥ 2`, `n - 1` and `n + 1` each have exactly one distinct
prime divisor, and at least one of `n - 1`, `n + 1` is composite. -/
def InSeq (n : ℕ) : Prop :=
  2 ≤ n ∧
  (n - 1).primeFactors.card = 1 ∧
  (n + 1).primeFactors.card = 1 ∧
  (¬ (n - 1).Prime ∨ ¬ (n + 1).Prime)

theorem main :
    Set.Infinite {n : ℕ | InSeq n} ∧
    Set.Finite {n : ℕ | InSeq n ∧ ¬ (n - 1).Prime ∧ ¬ (n + 1).Prime} := by
  sorry

end OMA.S_oeis_a088072
