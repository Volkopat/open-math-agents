import Mathlib.Data.Nat.Sqrt

/-! OEIS A034097. The decimal digit test is the units digit of the integer
square root of 100*n. The interval is maximal at both ends, and its stated
rounded length is written with exact natural-number division.
Source: https://oeis.org/A034097
Credit: @DomTheDeveloper -/

namespace OMA.S_oeis_a034097

theorem main : ∀ n : ℕ, (100*n).sqrt % 10 = 1 →
    ∃ lo hi : ℕ, 0 < lo ∧ lo ≤ n ∧ n ≤ hi ∧
      (∀ j : ℕ, lo ≤ j → j ≤ hi → (100*j).sqrt % 10 = 1) ∧
      (100*(lo-1)).sqrt % 10 ≠ 1 ∧ (100*(hi+1)).sqrt % 10 ≠ 1 ∧
      hi+1-lo = (10*n.sqrt+27)/50 := by
  sorry

end OMA.S_oeis_a034097
