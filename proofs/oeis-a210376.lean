import OMAStatements.S_oeis_a210376
import Mathlib

/-!
# A210376: 2 × 2 matrices over `{0, …, n}` with entry sum `n + 4` — the statement is false

The three claims are inconsistent with the actual value `a 2 = 10`.  The cubic formula
(valid for `n > 2`) gives `a 3 = 40`, `a 4 = 85`, `a 5 = 140`, `a 6 = 206`, and then the
recurrence at `n = 6` (claimed for all `n > 4`) would force
`a 2 = 4 * 140 - 6 * 85 + 4 * 40 - 206 = 4`.  But there are exactly ten matrices with entries
in `{0, 1, 2}` and entry sum `6`.  (The generating function has numerator of degree `6`, so the
recurrence really only starts at `n = 7`.)
-/

namespace OMA.S_oeis_a210376

/-- Direct count: ten matrices with entries in `{0, 1, 2}` have entry sum `6`. -/
lemma a_two : a 2 = 10 := by
  unfold a
  decide

end OMA.S_oeis_a210376

open OMA.S_oeis_a210376 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a210376.main) := by
  rintro ⟨-, hcubic, hrec⟩
  have h3 := hcubic 3 (by norm_num)
  have h4 := hcubic 4 (by norm_num)
  have h5 := hcubic 5 (by norm_num)
  have h6 := hcubic 6 (by norm_num)
  have h := hrec 6 (by norm_num)
  have h2 : (a 2 : ℤ) = 10 := by rw [a_two]; rfl
  norm_num at h3 h4 h5 h6 h
  linarith
