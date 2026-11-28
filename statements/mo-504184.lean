import Mathlib

/-!
# Congruence restrictions on prime divisors of polynomial values

Source: Euro Vidal Sampaio, MathOverflow question 504184 (CC BY-SA 4.0).
https://mathoverflow.net/questions/504184/congruence-restrictions-on-prime-divisors-of-polynomial-values
Lean statement: @MacChan1203.
-/

namespace OMA.S_mo_504184

theorem main :
    Set.Infinite {x : ℤ | ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x ^ 2 + 1 → p % 3 ≠ 1} := by
  sorry

end OMA.S_mo_504184
