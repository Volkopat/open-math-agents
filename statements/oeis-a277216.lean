import Mathlib

/-!
# Fixed points of OEIS A277216

Jaroslav Krizek conjectured that the product of the decimal digits of the sum
of the positive divisors of a positive integer equals that integer exactly
at 1 and 210.

Source: https://oeis.org/A277216 (OEIS Foundation, CC BY-SA 4.0).
Credit: @liuriloami
-/

namespace OMA.S_oeis_a277216

theorem main :
    ∀ n : ℕ, 0 < n →
      ((Nat.digits 10 (ArithmeticFunction.sigma 1 n)).prod = n ↔ n = 1 ∨ n = 210) := by
  sorry

end OMA.S_oeis_a277216
