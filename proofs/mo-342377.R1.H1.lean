import OMAReductions.R_mo_342377_R1

theorem OMA.solution : OMA.R_mo_342377_R1.H1 := by
  intro a b c d ha hc hd hbd h
  have e (x) : Nat.ascFactorial x 2 = x * (x + 1) := by simp [Nat.ascFactorial]; ring
  have t (x y) (hy : 3 ≤ y) : 3 ∣ Nat.ascFactorial x y :=
    (Nat.dvd_factorial (by norm_num) hy).trans (Nat.factorial_dvd_ascFactorial x y)
  rcases hbd with hb | ⟨rfl, rfl⟩
  · have := t a b hb
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · obtain rfl : d = 2 := by omega
      rw [h, e, Nat.dvd_iff_mod_eq_zero] at this
      rcases (by omega : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2) with h0 | h0 | h0 <;>
        simp [Nat.add_mod, Nat.mul_mod, h0] at this
    · have := t c d hd3; omega
  · rw [e, e] at h
    rcases (by omega : a ≤ c ∨ a = c + 1 ∨ c + 2 ≤ a) with h1 | rfl | h1 <;> nlinarith
