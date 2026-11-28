import Mathlib

/-!
# A093328: a(n) = 2*n^2 + 3.

Source: https://oeis.org/A093328
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a093328

def a (n : ℕ) : ℕ :=
  2 * n ^ 2 + 3

def IsPerfectPower (n : ℕ) : Prop :=
  ∃ k m : ℕ, 1 < k ∧ 1 < m ∧ k ^ m = n

theorem main : ∀ n : ℕ, ¬ IsPerfectPower (a n) := by
  sorry

end OMA.S_oeis_a093328
