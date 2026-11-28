import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Bounds.Defs

/-!
# A divisibility question about powers with exponent 4k+2

Source: Amir Baghban, https://mathoverflow.net/questions/258852
Lean statement: @huurou
-/

namespace OMA.S_mo_258852

def term (k : ℕ) : ℕ := 2 ^ (4 * k + 2) + 1

/-- If the smaller divisor contains the largest prime factor of the multiple,
are the two terms necessarily equal? -/
theorem main :
    ∀ m n : ℕ, 0 < m → 0 < n → term n ∣ term m →
      ∀ P : ℕ, IsGreatest {p : ℕ | p.Prime ∧ p ∣ term m} P →
        P ∣ term n → term n = term m := by
  sorry

end OMA.S_mo_258852
