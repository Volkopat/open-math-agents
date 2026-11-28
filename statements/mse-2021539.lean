import Mathlib

/-!
# Is there a maximal prime that is not a sum of consecutive primes?

Source: https://math.stackexchange.com/questions/2021539
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `𝒮` be the set of primes of the form `pₙ + p_{n+1} + ⋯ + p_{n+m}` with `m, n` positive
integers (sums of at least two consecutive primes). Question: is there a maximal prime not in `𝒮`
(equivalently, are all sufficiently large primes in `𝒮`)? `main` states the answer yes.

Conventions:
* `pₙ = Nat.nth Nat.Prime (n - 1)` (`p₁ = 2`); `m ≥ 1`, `n ≥ 1`.
-/

namespace OMA.S_mse_2021539

/-- `p` is a sum of at least two consecutive primes. -/
def InS (p : ℕ) : Prop :=
  ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ p = ∑ i ∈ Finset.range (m + 1), Nat.nth Nat.Prime (n - 1 + i)

/-- Only finitely many primes are not sums of consecutive primes. -/
theorem main : {p : ℕ | p.Prime ∧ ¬ InS p}.Finite := by
  sorry

end OMA.S_mse_2021539
