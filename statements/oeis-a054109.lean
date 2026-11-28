import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# OEIS A054109: Mathar's recurrence
Source: https://oeis.org/A054109 (OEIS Foundation, CC BY-SA 4.0).
Offset zero; terms begin 1, 2, 8, 27, 99.
We use Paul Barry's independent finite-sum formula (January 17, 2020),
also obtained by reversing the alternating sum defining T(2n+1,n) in A054106.
The conjecture is R. J. Mathar's recurrence (November 24, 2012), stated
for every n >= 2, exactly when all its indices are in the source domain.
The source still labels this identity a conjecture; no claim of mathematical
priority is made. A separate complete proof accompanies the review material.
-/
namespace OMA.S_oeis_a054109

def b (n : ℕ) : ℕ := (2 * n + 1).choose (n + 1)

def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (b k : ℤ)

theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) * a n + (-3 * (n : ℤ) - 1) * a (n - 1) +
      2 * (-2 * (n : ℤ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a054109
