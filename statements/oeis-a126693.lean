import Mathlib

/-!
# A126693: Prime numbers p such that 10000-p is also a prime

Source: https://oeis.org/A126693
Credit: @xor2k

The entry's comment reads: Suggested by the Goldbach conjecture. The last term of this sequence is
a(254)=9941.

This comment is a remark; the Goldbach conjecture itself is NOT formalized. The precise claim it
makes, formalized here, is that the last term of the sequence is a(254) = 9941: the 254th term is
`9941` and no term exceeds `9941` (so the sequence has exactly 254 terms).

Conventions:
* Offset 1, so `a(254)` is `Nat.nth IsTerm 253` (`Nat.nth` is 0-indexed and enumerates the terms in
  increasing order).
* `p` is a term iff `p` and `10000 - p` are both prime. Natural subtraction truncates to `0` for
  `p > 10000`, and `0` is not prime, so this agrees with the integer reading.
-/

namespace OMA.S_oeis_a126693

/-- `p` is a term of A126693: `p` and `10000 - p` are both prime. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ (10000 - p).Prime

/-- The last term of A126693 is `a(254) = 9941`. -/
theorem main :
    Nat.nth IsTerm 253 = 9941 ∧ ∀ p : ℕ, IsTerm p → p ≤ 9941 := by
  sorry

end OMA.S_oeis_a126693
