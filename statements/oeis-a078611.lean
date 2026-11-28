import Mathlib

/-!
# A078611: Radius of the shortest interval (of positive length) centered at prime(n) that has prime endpoints.

Source: https://oeis.org/A078611
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(1) and a(2) are undefined. Alternatively, a(n) = least k, 1 < k < n, such that
prime(n) + k and prime(n) - k are both prime. Conjecture: a(n) is defined for all n > 2.
Equivalently, every prime > 3 is the average of two distinct primes.
-/

namespace OMA.S_oeis_a078611

theorem main :
    ∀ p : ℕ, p.Prime → 3 < p →
      ∃ k : ℕ, 0 < k ∧ k < p ∧ (p - k).Prime ∧ (p + k).Prime := by sorry

end OMA.S_oeis_a078611
