import Mathlib

/-!
# A238939: Powers of 3 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A238939
Credit: @keiichisince1986-bot

A238939 lists the powers of 3 whose decimal expansion has no digit `0`. Its data are the 23 terms
`1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 177147, 531441, 1594323, 4782969, 1162261467,`
`94143178827, 282429536481, 2541865828329, 7625597484987, 22876792454961, 617673396283947,`
`16677181699666569, 278128389443693511257285776231761`.
The entry states: Conjectured to be finite and complete.

Conventions:
- Complete means that the data list every term. So the conjecture says that the set of powers
  of 3 without a digit `0` is exactly the set of these 23 numbers (which in particular makes it
  finite).
- The entry gives the formula `a(n) = 3^A030700(n)`, where A030700 lists the exponents
  `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 19, 23, 24, 26, 27, 28, 31, 34, 68`.
  The right-hand side of `main` is the image of this exponent set under `k ↦ 3 ^ k`; these 23
  powers are exactly the 23 numbers listed above.
- The data start with `1 = 3^0`, so the powers of 3 are `3 ^ k` for every `k : ℕ`.
- A natural number `m` has no digit `0` in its decimal expansion when `0 ∉ Nat.digits 10 m`.
  `Nat.digits 10` lists the decimal digits without leading zeros, so this is exactly the
  property in the name of the sequence.
-/

namespace OMA.S_oeis_a238939

theorem main :
    {m : ℕ | (∃ k : ℕ, m = 3 ^ k) ∧ 0 ∉ Nat.digits 10 m} =
      (fun k : ℕ => 3 ^ k) ''
        ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 19, 23, 24, 26, 27, 28, 31, 34, 68} :
          Set ℕ) := by
  sorry

end OMA.S_oeis_a238939
