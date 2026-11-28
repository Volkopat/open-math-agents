import Mathlib

/-!
# A037055: Smallest prime containing exactly n 1's

Source: https://oeis.org/A037055

Conjecture (OEIS A037055):
For every `n > 1`, the smallest prime whose base-10 representation contains
exactly `n` digits equal to `1` (OEIS A037055) coincides with the smallest prime
whose base-10 representation contains some digit exactly `n` times (OEIS A084673).

Conventions:
- For `n = 1`: `A037055(1) = 13` whereas `A084673(1) = 2`.
- For `n = 2, 3, 4, 5, 6`: both sequences equal `11, 1117, 10111, 101111, 1111151`.
- Expressed via `IsLeast` on both sets so no existence proof is required for `Nat.find`.
-/

namespace OMA.S_oeis_a037055

/-- Predicate stating that `p` has exactly `n` occurrences of the digit `1` in base 10. -/
def hasNDigits1 (n p : ℕ) : Prop :=
  (Nat.digits 10 p).count 1 = n

/-- Predicate stating that some decimal digit `d < 10` occurs exactly `n` times in `p`. -/
def hasSomeDigitNTimes (n p : ℕ) : Prop :=
  ∃ d : ℕ, d < 10 ∧ (Nat.digits 10 p).count d = n

/-- Conjecture: for all `n > 1`, A037055(n) = A084673(n). -/
theorem main :
    ∀ n p : ℕ, 1 < n →
      (IsLeast {q : ℕ | Nat.Prime q ∧ hasNDigits1 n q} p ↔
        IsLeast {q : ℕ | Nat.Prime q ∧ hasSomeDigitNTimes n q} p) := by
  sorry

end OMA.S_oeis_a037055
