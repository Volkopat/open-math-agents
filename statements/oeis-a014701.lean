import Mathlib

/-!
# A014701: Number of multiplications to compute n-th power by the Chandah-sutra method

Source: https://oeis.org/A014701
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (proved):
Let `a(n)` be the number of multiplications to compute the `n`-th power by the
Chandah-sutra (binary exponentiation) method: `a(1) = 0`, `a(2n) = a(n) + 1`,
`a(2n+1) = a(n) + 2` for `n ≥ 1`.
Then `a(n + 1)` is the minimal number of steps to go from `0` to `n` by choosing
before each step (after the first step) whether to keep the same step length or
double it, starting with initial step length `1`.
-/

namespace OMA.S_oeis_a014701

/-- Number of multiplications to compute the `n`-th power by the Chandah-sutra method. -/
def chandah (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else if n % 2 = 0 then chandah (n / 2) + 1
  else chandah (n / 2) + 2

/-- Consecutive step lengths either stay equal or double. -/
def stepChain : List ℕ → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => (v = u ∨ v = 2 * u) ∧ stepChain (v :: rest)

/-- A valid sequence of step lengths starts with `1` (if nonempty) and satisfies `stepChain`. -/
def validSteps : List ℕ → Prop
  | [] => True
  | x :: xs => x = 1 ∧ stepChain (x :: xs)

/-- For every `n : ℕ`, `chandah (n + 1)` is the minimum number of valid steps summing to `n`. -/
theorem main :
    ∀ n : ℕ,
      IsLeast { k : ℕ | ∃ s : List ℕ, validSteps s ∧ s.sum = n ∧ s.length = k }
        (chandah (n + 1)) := by
  sorry

end OMA.S_oeis_a014701
