import Mathlib

/-!
# The limiting ratio in OEIS A133470

Source: https://oeis.org/A133470 (Philippe Lallouet).
Credit: @asher-lanzone
-/

namespace OMA.S_oeis_a133470

noncomputable def b (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, ((j : ℝ) + 1) / (j + 3)

/-- The candidate index is `j + 2`, so that the first eligible integer is 2. -/
def flat (j : ℕ) : Prop := ⌊b (j + 2)⌋ = ⌊b (j + 1)⌋

/-- Zero-based enumeration: `term 0` is the OEIS term `a(1)`. -/
noncomputable def term (n : ℕ) : ℕ := Nat.nth flat n + 2

theorem main :
    Filter.Tendsto (fun n : ℕ ↦ (term (n + 1) : ℝ) / term n)
      Filter.atTop (nhds (Real.sqrt (Real.exp 1))) := by
  sorry

end OMA.S_oeis_a133470
