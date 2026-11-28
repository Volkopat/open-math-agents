import Mathlib

/-!
# A030063: Fermat's Diophantine m-tuple: 1 + the product of any two distinct terms is a square.

Source: https://oeis.org/A030063
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a030063

def IsDiophantineFiveTuple (s : Finset ℕ) : Prop :=
  s.card = 5 ∧ (∀ x ∈ s, 0 < x) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsSquare (x * y + 1)

theorem main : ¬ ∃ s : Finset ℕ, IsDiophantineFiveTuple s := by
  sorry

end OMA.S_oeis_a030063
