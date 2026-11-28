import Mathlib

/-!
# A245569: Numbers n such that binomial(2^n-1,n) is squarefree.

Source: https://oeis.org/A245569
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a245569

def IsTerm (n : ℕ) : Prop :=
  Squarefree (Nat.choose (2 ^ n - 1) n)

theorem main : Set.Finite {n : ℕ | IsTerm n} := by
  sorry

end OMA.S_oeis_a245569
