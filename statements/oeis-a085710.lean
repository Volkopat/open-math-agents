import Mathlib

/-!
# A085710: Smallest k such that kn+1 is a semiprime.

Source: https://oeis.org/A085710
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a085710

/-- `m` is a semiprime: a product of exactly two primes, not necessarily distinct
(`Ω m = 2`, i.e. `m` has exactly two prime factors counted with multiplicity). -/
def IsSemiprime (m : ℕ) : Prop := ArithmeticFunction.cardFactors m = 2

/-- Conjecture (A085710): for every `n > 2` there exists `k` with `0 < k < n` such that `n * k + 1` is a
semiprime. (`k > 0` since A085710 defines a(n) as the smallest `k ≥ 1`.) -/
theorem main : ∀ n : ℕ, 2 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSemiprime (n * k + 1) := by
  sorry

end OMA.S_oeis_a085710
