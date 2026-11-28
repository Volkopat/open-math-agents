import OMAStatements.S_oeis_a270211

open OMA.S_oeis_a270211

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270211.main) := by
  intro h
  have impossible : (3 : ℚ) * (a 6 : ℚ) = 15755 := by
    rw [h 6 (by decide)]
    norm_num
  have integral : 3 * a 6 = 15755 := by exact_mod_cast impossible
  omega
