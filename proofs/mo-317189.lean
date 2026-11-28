import OMAStatements.S_mo_317189

open Pointwise in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_317189.main) :=
  fun h => absurd (h {0, 1, 3, 4} (by decide)) (by decide)
