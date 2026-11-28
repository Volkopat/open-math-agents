import OMAReductions.R_Erdos364_erdos_364_R1

theorem OMA.solution : OMA.R_Erdos364_erdos_364_R1.H1 := by
  rintro n h ⟨a, b, c⟩
  have p (m) (hm : Nat.Powerful m) : m % 4 ≠ 2 := fun h => by
    have := hm 2 (Nat.mem_primeFactors.2 ⟨Nat.prime_two, by omega, by omega⟩)
    omega
  have := p _ a
  have := p _ b
  have := p _ c
  omega
