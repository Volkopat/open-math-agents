import OMAStatements.S_mo_473367
open OMA.S_mo_473367 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_473367.main) := by
  intro h
  have := h 3 !![0, -1, 1; -1, 0, 1; 1, 1, 0] (by decide) (by unfold Matrix.of; decide) (by unfold Matrix.of; decide) (by decide) ![1, -1, 0]
  norm_num [quadraticForm, OMA.S_mo_473367.Laplacian, Fin.sum_univ_three, Matrix.diagonal, Matrix.cons_val_two] at this
