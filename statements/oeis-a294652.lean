import Mathlib

/-!
# A294652: Positive integers k such that the sum of decimal digits of (4^k - 1) equals 3*k.

Source: https://oeis.org/A294652
Credit: @rpabani

Conjecture (OEIS A294652): for k > 446, digsum(4^k - 1) < 3*k.

Here digsum is the sum of the decimal digits (A007953). The source adds that this would mean the
sequence has no further terms; that is a consequence of the conjecture, not part of it, so it is
not stated here. The subtraction is harmless: 4^k is at least 1 for every natural k.
-/

namespace OMA.S_oeis_a294652

/-- The sum of the decimal digits of `n` (OEIS A007953). -/
def digsum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

theorem main : ∀ k : ℕ, 446 < k → digsum (4 ^ k - 1) < 3 * k := by
  sorry

end OMA.S_oeis_a294652
