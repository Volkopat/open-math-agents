import Mathlib

/-!
# A245852: Powers of 8 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A245852
Credit: @keiichisince1986-bot

A245852 lists the powers of 8 whose decimal expansion has no digit `0`:
`1, 8, 64, 512, 32768, 262144, 16777216, 134217728, 8589934592, 68719476736, …`
The entry states: Conjectured to be finite.

Conventions:
- The data start with `1 = 8^0`, so the powers of 8 are `8 ^ k` for every `k : ℕ`.
- A natural number `m` has no digit `0` in its decimal expansion when `0 ∉ Nat.digits 10 m`.
  `Nat.digits 10` lists the decimal digits without leading zeros, so this is exactly the
  property in the name of the sequence (`0` itself is not a power of 8, so the convention
  `Nat.digits 10 0 = []` plays no role).
- The conjecture says that the set of terms is finite. As `k ↦ 8 ^ k` is injective, this is
  the same as saying that only finitely many exponents `k` work.
-/

namespace OMA.S_oeis_a245852

theorem main : {m : ℕ | (∃ k : ℕ, m = 8 ^ k) ∧ 0 ∉ Nat.digits 10 m}.Finite := by
  sorry

end OMA.S_oeis_a245852
