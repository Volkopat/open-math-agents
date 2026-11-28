import OMAReductions.R_mo_342377_R1

/-! If b ≥ 3, then 3 divides b!, which divides a(a+1)⋯(a+b-1). The product c(c+1)⋯(c+d-1) with
d ≥ 2 is 0 or 2 modulo 3 (it is divisible by 3 when d ≥ 3, and equals c(c+1) when d = 2), so
adding 2 never gives a multiple of 3. If b = d = 2, then a(a+1) = c(c+1) + 2 forces a = c + 1
and then c = 0, contradicting c ≥ 2. -/

theorem OMA.solution : OMA.R_mo_342377_R1.H1 := by
  intro a b c d ha hc hd hbd h
  have e2 : ∀ x : ℕ, Nat.ascFactorial x 2 = x * (x + 1) := by
    intro x
    simp [Nat.ascFactorial]
    ring
  rcases hbd with hb | ⟨rfl, rfl⟩
  · have h3a : 3 ∣ Nat.ascFactorial a b :=
      (Nat.dvd_factorial (by norm_num) hb).trans (Nat.factorial_dvd_ascFactorial a b)
    have hr : (Nat.ascFactorial c d + 2) % 3 ≠ 0 := by
      rcases Nat.lt_or_ge d 3 with hd3 | hd3
      · obtain rfl : d = 2 := by omega
        rw [e2]
        have hc3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
        rcases hc3 with h0 | h0 | h0 <;> simp [Nat.add_mod, Nat.mul_mod, h0]
      · have : 3 ∣ Nat.ascFactorial c d :=
          (Nat.dvd_factorial (by norm_num) hd3).trans (Nat.factorial_dvd_ascFactorial c d)
        omega
    omega
  · rw [e2, e2] at h
    rcases (by omega : a ≤ c ∨ a = c + 1 ∨ c + 2 ≤ a) with h1 | h1 | h1
    · nlinarith
    · subst h1
      nlinarith
    · nlinarith
