import OMAStatements.S_oeis_a225663
import Mathlib.Tactic

-- The base-five digits of 1976724 contain two copies of each digit.
-- At step 9 the vector is [0,2,1]. Step 10 starts the six-cycle at [1,1,1].
open OMA.S_oeis_a225663

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a225663.main) := by
  intro h
  have enters : hasPreperiod (digits 1976724) 10 := by
    unfold hasPreperiod
    decide +kernel
  have impossible := h 1976724 10 enters (by decide)
  exact (by decide : ¬ Odd (10 : ℕ)) impossible
