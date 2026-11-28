import Mathlib

/-!
# A059850: Decimal expansion of Pi^e.

Source: https://oeis.org/A059850
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a059850

/-- OEIS A059850: `Pi^e` is conjectured to be transcendental over the rationals. -/
theorem main : Transcendental ℚ (Real.pi ^ Real.exp 1) := by
  sorry

end OMA.S_oeis_a059850
