import Mathlib

/-!
# A253644: Numbers n such that n^k is zeroless for k=0,...,5.

Source: https://oeis.org/A253644
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a253644

def Zeroless (n : ℕ) : Prop :=
  n ≠ 0 ∧ 0 ∉ Nat.digits 10 n

def IsTerm (n : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ 5 → Zeroless (n ^ k)

theorem main : Set.Finite {n : ℕ | IsTerm n} := by
  sorry

end OMA.S_oeis_a253644
