import Mathlib

/-!
# A272322: Numbers n such that n^n does not contain all ten decimal digits.

Source: https://oeis.org/A272322
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a272322

def IsTerm (n : ℕ) : Prop :=
  ∃ d : ℕ, d < 10 ∧ d ∉ Nat.digits 10 (n ^ n)

theorem main : ∀ n : ℕ, 40 < n → IsTerm n → ∃ k : ℕ, n = 10 ^ k := by
  sorry

end OMA.S_oeis_a272322
