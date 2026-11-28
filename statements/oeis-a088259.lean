import Mathlib

/-!
# A088259: Perfect powers which have at least one prime neighbor.

Source: https://oeis.org/A088259
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a088259

def IsPerfectPower (n : ℕ) : Prop :=
  ∃ k m : ℕ, 1 < k ∧ 1 < m ∧ k ^ m = n

def IsTerm (n : ℕ) : Prop :=
  IsPerfectPower n ∧ ((n - 1).Prime ∨ (n + 1).Prime)

theorem main : Set.Infinite {n : ℕ | IsTerm n} := by
  sorry

end OMA.S_oeis_a088259
