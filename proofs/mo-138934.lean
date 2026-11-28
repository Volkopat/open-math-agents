import OMAStatements.S_mo_138934
import Mathlib

open Polynomial in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_138934.main) := fun h => by
  obtain ⟨n, hn, hi⟩ := h ℚ 1 (-2) one_ne_zero (neg_ne_zero.2 two_ne_zero)
  have := coeff_eq_zero_of_degree_lt (n := n) ((degree_eq_one_of_irreducible_of_root hi (x := 1) (by norm_num [map_ofNat])).trans_lt (by exact_mod_cast hn))
  simp [coeff_X, coeff_C, hn.ne, (zero_lt_one.trans hn).ne'] at this
