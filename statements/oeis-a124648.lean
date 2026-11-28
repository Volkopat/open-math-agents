import Mathlib

/-!
# A124648: Numbers n such that n^i (i=1..7) are all zeroless.

Source: https://oeis.org/A124648
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a124648

def Zeroless (n : ℕ) : Prop :=
  n ≠ 0 ∧ 0 ∉ Nat.digits 10 n

def IsTerm (n : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ 7 → Zeroless (n ^ i)

theorem main : Set.Finite {n : ℕ | IsTerm n} := by
  sorry

end OMA.S_oeis_a124648
