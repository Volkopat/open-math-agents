import OMAStatements.S_mo_335876
import Mathlib

open Filter

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_335876.main) := fun h => one_ne_zero <| h ℝ abs 0 (.of_forall (by simp)) 1 1 <| tendsto_const_nhds.congr' <| eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => by simp [abs_of_pos ht, ht.ne']
