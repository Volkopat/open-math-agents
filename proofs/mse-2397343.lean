import OMAStatements.S_mse_2397343
import Mathlib

-- Credit: @tjgksruf9801 (shorter proof). Same 8-variable instance: linearly satisfiable over
-- ZMod 3 by (1, 0, 1, 1, 0, 0, 0, 2) but not Boolean satisfiable.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2397343.main) := fun h => by
  have := (h 8 {{0, 1, 2}, {0, 1, 3}, {2, 3, 4}, {2, 3, 5}, {2, 3, 6}, {5, 6, 7}}
    (by decide +kernel)).2 (.intro (![1, 0, 1, 1, 0, 0, 0, 2]) (by decide +kernel))
  revert this
  unfold OMA.S_mse_2397343.BooleanSatisfiable
  decide +kernel
