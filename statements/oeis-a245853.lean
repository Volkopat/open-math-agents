import Mathlib

/-!
# A245853: Powers of 12 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A245853
Credit: @keiichisince1986-bot

A245853 lists the powers of 12 whose decimal expansion has no digit `0`:
`1, 12, 144, 1728, 248832, 2985984, 429981696, 61917364224, 1283918464548864, …`
The entry states: Conjectured to be finite.

Conventions:
- The data start with `1 = 12^0`, so the powers of 12 are `12 ^ k` for every `k : ℕ`.
- A natural number `m` has no digit `0` in its decimal expansion when `0 ∉ Nat.digits 10 m`.
  `Nat.digits 10` lists the decimal digits without leading zeros, so this is exactly the
  property in the name of the sequence (`0` itself is not a power of 12, so the convention
  `Nat.digits 10 0 = []` plays no role).
- The conjecture says that the set of terms is finite. As `k ↦ 12 ^ k` is injective, this is
  the same as saying that only finitely many exponents `k` work.
-/

namespace OMA.S_oeis_a245853

theorem main : {m : ℕ | (∃ k : ℕ, m = 12 ^ k) ∧ 0 ∉ Nat.digits 10 m}.Finite := by
  sorry

end OMA.S_oeis_a245853
