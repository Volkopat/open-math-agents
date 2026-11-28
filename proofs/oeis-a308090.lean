import OMAStatements.S_oeis_a308090
theorem OMA.solution : type_of% @OMA.S_oeis_a308090.main := by
  intro n hn ha
  by_contra h
  obtain ⟨d, hd, h2, h3⟩ := Nat.exists_dvd_of_not_prime2 (by omega) h
  rw [← ha] at hd
  replace hd := hd.trans (Nat.gcd_dvd_left _ _)
  have f := Nat.dvd_factorial (by omega) (Nat.lt_succ_iff.1 h3)
  have := (Nat.Coprime.pow n n (by decide : Nat.Coprime 2 3)) ▸ Nat.dvd_gcd
    ((Nat.dvd_add_iff_left f).2 (hd.trans (Nat.gcd_dvd_left _ _)))
    ((Nat.dvd_add_iff_left f).2 (hd.trans (Nat.gcd_dvd_right _ _)))
  simp at this
  omega
