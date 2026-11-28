import OMAStatements.S_oeis_a299017
import Mathlib.Tactic

/-! The closed formula fixes terms four, five and six at 10, 21 and 36.
Running the proposed recurrence backwards at six and five forces the third
term to equal 3 and the second term to vanish. The intersection is listed
in strictly increasing order, so its second term must be positive. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a299017.main) := by
  rintro ⟨a, _, increasing, _, _, formula, recurrence⟩
  have fourth := formula 4 (by decide)
  have fifth := formula 5 (by decide)
  have sixth := formula 6 (by decide)
  have atFive := recurrence 5 (by decide)
  have atSix := recurrence 6 (by decide)
  norm_num at fourth fifth sixth atFive atSix
  have strict := increasing (show (1 : ℕ) < 2 by decide)
  omega
