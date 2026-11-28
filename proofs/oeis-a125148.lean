import OMAStatements.S_oeis_a125148

theorem OMA.solution : type_of% @OMA.S_oeis_a125148.main := by
  intro x hx hodd hfive
  have hcop : x.Coprime 10 := hodd.coprime_two_right.mul_right
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hfive).symm
  obtain ⟨p, hgt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq x (by decide : 10 ≠ 0) hcop
  refine ⟨p, p-x, hp, by omega, ?_, by omega⟩
  exact (Nat.modEq_iff_dvd' hgt.le).mp hmod.symm