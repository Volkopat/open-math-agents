import Mathlib

/-!
# A238936: Powers of 6 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A238936
Credit: @keiichisince1986-bot

A238936 lists the powers of 6 whose decimal expansion has no digit `0`. Its data are the 14 terms
`1, 6, 36, 216, 1296, 7776, 46656, 279936, 1679616, 2176782336, 16926659444736,`
`4738381338321616896, 36845653286788892983296, 17324272922341479351919144385642496`.
The entry states: Conjectured to be finite and complete.

Conventions:
- Complete means that the data list every term. So the conjecture says that the set of powers
  of 6 without a digit `0` is exactly the set of these 14 numbers (which in particular makes it
  finite).
- The entry gives the formula `a(n) = 6^A030702(n)`, where A030702 lists the exponents
  `0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 17, 24, 29, 44`.
  The right-hand side of `main` is the image of this exponent set under `k ↦ 6 ^ k`; these 14
  powers are exactly the 14 numbers listed above.
- The data start with `1 = 6^0`, so the powers of 6 are `6 ^ k` for every `k : ℕ`.
- A natural number `m` has no digit `0` in its decimal expansion when `0 ∉ Nat.digits 10 m`.
  `Nat.digits 10` lists the decimal digits without leading zeros, so this is exactly the
  property in the name of the sequence.
-/

namespace OMA.S_oeis_a238936

theorem main :
    {m : ℕ | (∃ k : ℕ, m = 6 ^ k) ∧ 0 ∉ Nat.digits 10 m} =
      (fun k : ℕ => 6 ^ k) '' ({0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 17, 24, 29, 44} : Set ℕ) := by
  sorry

end OMA.S_oeis_a238936
