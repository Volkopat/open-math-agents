import Mathlib

/-!
# A014945: Numbers k such that k divides 4^k - 1.

Source: https://oeis.org/A014945
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a014945

theorem main : ∀ k : ℕ, 0 < k → k ∣ 4 ^ k - 1 →
    Squarefree ((4 ^ k - 1) / k) := by
  sorry

end OMA.S_oeis_a014945
