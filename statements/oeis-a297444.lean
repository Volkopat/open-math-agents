import Mathlib

/-!
# OEIS A297444

Source: https://oeis.org/A297444 (OEIS Foundation, CC BY-SA 4.0).
Clark Kimberling conjectures that the sequence enumerates the least positive integers
having each prescribed ternary down-variation. The down-variation is the sum of
decreases while reading the digits from most to least significant, as in A297441.
The recurrence applies after the four listed initial values.
-/

namespace OMA.S_oeis_a297444

/-- The sequence with the initial values and recurrence from A297444. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 33
  | n + 4 => a (n + 3) + 9 * a (n + 2) - 9 * a (n + 1)

/-- Decreases between adjacent digits in a list stored least significant first. -/
def down : List ℕ → ℕ
  | x :: y :: rest => (y - x) + down (y :: rest)
  | _ => 0

/-- Ternary down-variation of a natural number. -/
def downVar (m : ℕ) : ℕ := down (Nat.digits 3 m)

/-- Kimberling's conjecture, including the positive minimum for zero variation. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ, (m : ℤ) = a n ∧
    IsLeast {k : ℕ | 0 < k ∧ downVar k = n} m := by
  sorry

end OMA.S_oeis_a297444
