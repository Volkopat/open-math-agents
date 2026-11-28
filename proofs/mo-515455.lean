import OMAStatements.S_mo_515455
import Mathlib



open OMA.S_mo_515455



theorem OMA.solution : type_of% @OMA.S_mo_515455.main := by
  -- Vepir gives these four integers in the answer to MathOverflow question 515455.
  refine ⟨-453120488918163043957285, -410185594882463784982184,
    243023758759477967211040, 182420312468292386328040, ?_⟩
  norm_num
