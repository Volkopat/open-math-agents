import Mathlib

/-!
# The corrected divisibility exercise in MathOverflow 16341

The May 2015 revision gives the corrected second-edition exercise from
Andreescu and Dospinescu: classify the positive integer pairs (m,n) such
that m²−1 divides 3^m+(n!−2)^m. The factorial subtraction takes place
in the integers, so its value at n=1 is −1.

Source: https://mathoverflow.net/questions/16341 (CC BY-SA)
Credit: @connoranderson
-/

namespace OMA.S_mo_16341

theorem main : ∀ (m n : ℕ), 0 < m → 0 < n →
    (((m:ℤ)^2-1 ∣ (3:ℤ)^m+((n.factorial:ℤ)-2)^m) ↔ (m=2 ∧ n=2)) := by
  sorry

end OMA.S_mo_16341
