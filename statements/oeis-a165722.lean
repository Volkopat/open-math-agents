import Mathlib

/-!
# A165722: Positive integers k such that the sum of decimal digits of (16^k - 1) equals 6*k.

Source: https://oeis.org/A165722
Credit: @rpabani

Conjecture (Iain Fox, Nov 22 2017): for k > 223, digsum(16^k - 1) < 6*k.

Here digsum is the sum of the decimal digits (A007953). The source adds that this would mean the
sequence has no terms beyond 223; that is a consequence of the conjecture, not part of it, so it is
not stated here. The subtraction is harmless: 16^k is at least 1 for every natural k.
-/

namespace OMA.S_oeis_a165722

/-- The sum of the decimal digits of `n` (OEIS A007953). -/
def digsum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

theorem main : ∀ k : ℕ, 223 < k → digsum (16 ^ k - 1) < 6 * k := by
  sorry

end OMA.S_oeis_a165722
