import Mathlib.Data.Nat.Digits.Defs

/-!
# OEIS A398769

Chai Wah Wu conjectured that every odd natural number divisible by the product
of its decimal digits times their sum contains the digit 1.

Source: https://oeis.org/A398769
-/

namespace OMA.S_oeis_a398769

theorem main : ∀ k : ℕ, k % 2 = 1 →
    (Nat.digits 10 k).prod * (Nat.digits 10 k).sum ∣ k →
    1 ∈ Nat.digits 10 k := by
  sorry

end OMA.S_oeis_a398769
