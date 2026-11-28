import OMAStatements.S_oeis_a227021
import Mathlib

open OMA.S_oeis_a227021

namespace W227021

/-- The two clauses of the statement at n = 8 and k = 1, with the sequence abstracted to `s`.
The first clause says the recurrence expression equals numerator 8 = 1, the second says it is 0.
Keeping `s` abstract stops the kernel from ever evaluating the sequence. -/
theorem key (s : ℕ → ℤ)
    (e1 : (((((((if 0 ≤ 8 then s (8 - 0) else 0) -
                6 * if 1 ≤ 8 then s (8 - 1) else 0) +
              15 * if 2 ≤ 8 then s (8 - 2) else 0) -
            20 * if 3 ≤ 8 then s (8 - 3) else 0) +
          15 * if 4 ≤ 8 then s (8 - 4) else 0) -
        6 * if 5 ≤ 8 then s (8 - 5) else 0) +
      if 6 ≤ 8 then s (8 - 6) else 0) =
      if 8 = 1 then 7 else if 8 = 2 then -16 else if 8 = 3 then 21 else if 8 = 4 then -11
      else if 8 = 5 then 7 else if 8 = 6 then -6 else if 8 = 8 then 1 else 0)
    (e2 : s (1 + 7) =
      6 * s (1 + 6) - 15 * s (1 + 5) + 20 * s (1 + 4) - 15 * s (1 + 3) + 6 * s (1 + 2) - s (1 + 1)) :
    False := by
  norm_num at e1 e2
  linarith

end W227021

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227021.main) :=
  fun h => W227021.key OMA.S_oeis_a227021.sequence (h.1 8) (h.2 1)
