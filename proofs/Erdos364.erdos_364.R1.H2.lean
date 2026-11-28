import OMAReductions.R_Erdos364_erdos_364_R1

-- Three consecutive powerful numbers n, n + 1, n + 2 need n = 0, 7 or 8 mod 9.

theorem OMA.solution : OMA.R_Erdos364_erdos_364_R1.H2 := by
  rintro n h0 h7 h8 ⟨p0, p1, p2⟩
  have f m (p : Nat.Powerful m) : m % 9 ≠ 3 ∧ m % 9 ≠ 6 := by
    by_contra h
    have := p 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by omega, by omega⟩)
    omega
  have := f n p0
  have := f (n + 1) p1
  have := f (n + 2) p2
  omega
