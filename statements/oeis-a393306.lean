import Mathlib

/-!
# OEIS A393306

In every base at least two, there is a largest pandigital number whose quotient by
the prescribed divisor is prime.

Source: https://oeis.org/A393306
Credit: @gblacher2
-/

namespace OMA.S_oeis_a393306

/-- The divisor in the prime test, with the factor of two canceled in odd bases. -/
def divisor (base : ℕ) : ℕ :=
  if Even base then base - 1 else (base - 1) / 2

def admissible (base k : ℕ) : Prop :=
  (Nat.digits base k).Perm (List.range base) ∧
    ∃ p : ℕ, p.Prime ∧ k = divisor base * p

theorem main : ∀ base : ℕ, 2 ≤ base →
    ∃ k : ℕ, IsGreatest {m | admissible base m} k := by
  sorry

end OMA.S_oeis_a393306
