import OMAStatements.S_oeis_a101042

theorem OMA.solution : type_of% @OMA.S_oeis_a101042.main := by
  intro q hq
  obtain ⟨r, hrq, hr, hm⟩ := Nat.forall_exists_prime_gt_and_modEq q (q - 1).factorial_ne_zero
    (hq.coprime_factorial_of_lt (by have := hq.two_le; omega))
  refine ⟨r - q, by omega, by rwa [Nat.add_sub_of_le hrq.le], fun p hp hpq h => ?_⟩
  exact (h.eq_one_or_self_of_dvd p ((Nat.dvd_add_right (dvd_refl p)).2
    ((Nat.dvd_factorial hp.pos (by omega)).trans hm.symm.dvd'))).elim hp.ne_one (by omega)
