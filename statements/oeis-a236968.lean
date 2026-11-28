import Mathlib

/-!
# A236968: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that 6*k - 1, 6*k + 1 and k + phi(m) are all prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236968
Credit: @keiichisince1986-bot

A236968 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 1. [The entry continues with a variant using phi(m)/2; only the
first claim is formalized here.]

Conventions:
- `phi` is `Nat.totient`; `6k - 1` with `k ≥ 1` is exact.
-/

namespace OMA.S_oeis_a236968

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      (6 * k - 1).Prime ∧ (6 * k + 1).Prime ∧ (k + Nat.totient m).Prime := by
  sorry

end OMA.S_oeis_a236968
