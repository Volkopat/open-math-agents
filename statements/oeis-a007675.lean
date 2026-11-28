import Mathlib

/-!
# A007675: Numbers m such that m, m+1 and m+2 are squarefree.

Source: https://oeis.org/A007675
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a007675

def primorial (p : ℕ) : ℕ :=
  (Finset.filter (fun q => Nat.Prime q) (Finset.range (p + 1))).prod id

theorem main : ∀ p : ℕ, Nat.Prime p →
    Squarefree (primorial p - 1) ∧ Squarefree (primorial p) ∧
      Squarefree (primorial p + 1) := by
  sorry

end OMA.S_oeis_a007675
