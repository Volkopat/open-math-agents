import Mathlib

/-!
# Decimal digits of palindromic primes with palindromic squares

Source: https://oeis.org/A225603
Credit: @laurilehtinen

The increasing sequence starts with 2 and 3 and has offset one. Thus the terms
at indices at least three are exactly its prime members greater than three.
Chai Wah Wu conjectured that all their decimal digits are zero or one.
-/

namespace OMA.S_oeis_a225603

theorem main :
    ∀ p : ℕ, p.Prime → 3 < p → (Nat.digits 10 p).Palindrome →
      (Nat.digits 10 (p^2)).Palindrome → ∀ d ∈ Nat.digits 10 p, d=0 ∨ d=1 := by
  sorry

end OMA.S_oeis_a225603

