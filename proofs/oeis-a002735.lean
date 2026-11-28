import OMAStatements.S_oeis_a002735

open OMA.S_oeis_a002735 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002735.main := by
  intro n hn
  rw [a, a, show 2 * n + 1 = 2 * n - 1 + 2 by omega, B, if_neg (by omega),
    show 2 * n - 1 + 1 = 2 * n by omega]
  norm_num
