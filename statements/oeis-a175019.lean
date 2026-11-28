import Mathlib

/-!
# OEIS A175019 and its four occurrence conjectures

Source: https://oeis.org/A175019 (OEIS Foundation, CC BY-SA 4.0).
Credit: @anmolspace.

José María Grau Ribas defined a(0)=a(1)=1 and a(n)=a(n-a(n-2))+2 for n≥2.
Chai Wah Wu proposed the four conclusions below in June 2016.
-/

namespace OMA.S_oeis_a175019

/-- The recurrence for the half-index b of the odd value a=2b+1.
Subtracting 2b+1 makes both nested recursive calls strictly smaller. -/
def half : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => half (n + 2 - (2 * half n + 1)) + 1
termination_by n => n
decreasing_by all_goals omega

/-- The original sequence. -/
def a (i : ℕ) : ℕ := 2 * half i + 1

/-- All indices at which the sequence attains the odd value 2n+1. -/
def positions (n : ℕ) : Set ℕ := {i | a i = 2 * n + 1}

theorem main :
    (∀ n : ℕ, (positions n).Nonempty) ∧
    (∀ n : ℕ, (positions n).encard = ((2 * n + 2 : ℕ) : ENat)) ∧
    (∀ n : ℕ, IsGreatest (positions n) ((n + 3) ^ 2 - 8)) ∧
    (∀ n : ℕ, 0 < n → IsLeast (positions n) ((n - 1) ^ 2 + 2)) := by
  sorry

end OMA.S_oeis_a175019
