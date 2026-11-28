import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Coprime values of 2ⁿ − 1 and 5ⁿ − 1

OEIS A265166 conjectures that infinitely many positive exponents give coprime
values. The sequence entry cites the Ailon–Rudnick conjecture.

Source: https://oeis.org/A265166
Credit: @hiattco
-/

namespace OMA.S_oeis_a265166

theorem main :
    Set.Infinite {n : ℕ | 0 < n ∧ Nat.Coprime (2 ^ n - 1) (5 ^ n - 1)} := by
  sorry

end OMA.S_oeis_a265166
