import Mathlib

/-!
# A238940: Powers of 4 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A238940
Credit: @keiichisince1986-bot

A238940 lists the powers of 4 whose decimal expansion has no digit `0`. Its data are the 16 terms
`1, 4, 16, 64, 256, 16384, 65536, 262144, 16777216, 268435456, 4294967296, 17179869184,`
`68719476736, 4722366482869645213696, 75557863725914323419136, 77371252455336267181195264`.
The entry states: Conjectured to be finite and complete.

Conventions:
- Complete means that the data list every term. So the conjecture says that the set of powers
  of 4 without a digit `0` is exactly the set of these 16 numbers (which in particular makes it
  finite).
- The entry gives the formula `a(n) = 4^A030701(n)`, where A030701 lists the exponents
  `0, 1, 2, 3, 4, 7, 8, 9, 12, 14, 16, 17, 18, 36, 38, 43`.
  The right-hand side of `main` is the image of this exponent set under `k ↦ 4 ^ k`; these 16
  powers are exactly the 16 numbers listed above.
- The data start with `1 = 4^0`, so the powers of 4 are `4 ^ k` for every `k : ℕ`.
- A natural number `m` has no digit `0` in its decimal expansion when `0 ∉ Nat.digits 10 m`.
  `Nat.digits 10` lists the decimal digits without leading zeros, so this is exactly the
  property in the name of the sequence.
-/

namespace OMA.S_oeis_a238940

theorem main :
    {m : ℕ | (∃ k : ℕ, m = 4 ^ k) ∧ 0 ∉ Nat.digits 10 m} =
      (fun k : ℕ => 4 ^ k) ''
        ({0, 1, 2, 3, 4, 7, 8, 9, 12, 14, 16, 17, 18, 36, 38, 43} : Set ℕ) := by
  sorry

end OMA.S_oeis_a238940
