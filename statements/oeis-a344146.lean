import Mathlib

/-!
# A344146: a(n) is the number of pentanomials x^n + x^a + x^b + x^c + 1 that are irreducible over GF(2) for n > a > b > c > 0.

Source: https://oeis.org/A344146
Credit: @keiichisince1986-bot

A344146 is the sequence `a(n)` named in the title. The entry states:
It is conjectured that a(n) > 0 for all n >= 4.

Conventions:
- GF(2) is `ZMod 2`; irreducibility is Mathlib's `Irreducible` in `Polynomial (ZMod 2)`.
- `a(n) > 0` means that `X^n + X^a + X^b + X^c + 1` is irreducible for some `n > a > b > c > 0`.
-/

namespace OMA.S_oeis_a344146

open Polynomial

theorem main :
    ∀ n : ℕ, 4 ≤ n → ∃ a b c : ℕ, 0 < c ∧ c < b ∧ b < a ∧ a < n ∧
      Irreducible (X ^ n + X ^ a + X ^ b + X ^ c + 1 : Polynomial (ZMod 2)) := by
  sorry

end OMA.S_oeis_a344146
