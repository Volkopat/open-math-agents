import Mathlib

/-!
# A034293: Numbers k such that 2^k does not contain the digit 2 (probably finite).

Source: https://oeis.org/A034293
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a034293

def IsTerm (k : ℕ) : Prop :=
  2 ∉ Nat.digits 10 (2 ^ k)

theorem main : IsTerm 168 ∧ ∀ k : ℕ, IsTerm k → k ≤ 168 := by
  sorry

end OMA.S_oeis_a034293
