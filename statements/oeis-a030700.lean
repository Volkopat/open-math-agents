import Mathlib

/-!
# A030700: Decimal expansion of 3^n contains no zeros (probably finite).

Source: https://oeis.org/A030700
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a030700

def IsTerm (n : ℕ) : Prop :=
  0 ∉ Nat.digits 10 (3 ^ n)

theorem main : IsTerm 68 ∧ ∀ n : ℕ, IsTerm n → n ≤ 68 := by
  sorry

end OMA.S_oeis_a030700
