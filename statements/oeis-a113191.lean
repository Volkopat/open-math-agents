import Mathlib

/-!
# A113191: Difference of two Lucas numbers.

Source: https://oeis.org/A113191
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a113191

def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

def IsPerfectPower (x : ℕ) : Prop :=
  ∃ a r : ℕ, 1 < a ∧ 1 < r ∧ x = a ^ r

theorem main : ∀ m n : ℕ, 1 < m → n < m →
    IsPerfectPower (lucas m - lucas n) → ¬ IsSquare (lucas m - lucas n) →
      (m = 7 ∧ n = 0) ∨ (m = 5 ∧ n = 2) := by
  sorry

end OMA.S_oeis_a113191
