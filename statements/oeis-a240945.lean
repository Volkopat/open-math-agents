import Mathlib

/-!
# A240945: Powers of 9 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A240945
Credit: @keiichisince1986-bot

A240945 lists the powers of 9 whose decimal expansion has no digit `0`:
`1, 9, 81, 729, 6561, 531441, 4782969, 282429536481, 2541865828329, …`
The entry states: Conjectured to be finite.

Conventions:
- The data start with `1 = 9^0`, so the powers of 9 are `9 ^ k` for every `k : ℕ`.
- A natural number `m` has no digit `0` in its decimal expansion when `0 ∉ Nat.digits 10 m`.
  `Nat.digits 10` lists the decimal digits without leading zeros, so this is exactly the
  property in the name of the sequence (`0` itself is not a power of 9, so the convention
  `Nat.digits 10 0 = []` plays no role).
- The conjecture says that the set of terms is finite. As `k ↦ 9 ^ k` is injective, this is
  the same as saying that only finitely many exponents `k` work.
-/

namespace OMA.S_oeis_a240945

theorem main : {m : ℕ | (∃ k : ℕ, m = 9 ^ k) ∧ 0 ∉ Nat.digits 10 m}.Finite := by
  sorry

end OMA.S_oeis_a240945
