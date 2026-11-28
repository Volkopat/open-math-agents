import Mathlib

/-!
# OEIS A101036: Riesel numbers without a covering set

Source: https://oeis.org/A101036
A Riesel number is an odd `n` such that `n·2^k - 1` is composite for all `k > 0`; A101036 lists
those that have a covering set. Conjecture (Filaseta et al., p. 16; recorded by Wesolowski):
there are infinitely many Riesel numbers that do not arise from a covering system.

Conventions. A covering set for `n` is a finite set `S` of primes such that every `n·2^k - 1`
(`k > 0`) is divisible by some `p ∈ S`. "Composite" means `> 1` and not prime.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a101036

/-- `n` is a Riesel number. -/
def IsRiesel (n : ℕ) : Prop :=
  Odd n ∧ ∀ k : ℕ, 0 < k → 1 < n * 2 ^ k - 1 ∧ ¬ (n * 2 ^ k - 1).Prime

/-- `n` has a covering set. -/
def HasCoveringSet (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ k : ℕ, 0 < k → ∃ p ∈ S, p ∣ n * 2 ^ k - 1

theorem main : {n : ℕ | IsRiesel n ∧ ¬ HasCoveringSet n}.Infinite := by
  sorry

end OMA.S_oeis_a101036
