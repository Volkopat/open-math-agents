import OMAReductions.R_CollatzConjecture_collatz_conjecture_R2_H2_R1

open CollatzConjecture

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1.H1 := by
  intro r hr hc hs
  have cert : ∀ r : Fin 1024,
      (r.val % 32 = 7 ∨ r.val % 32 = 15 ∨ r.val % 32 = 27 ∨ r.val % 32 = 31) →
      r.val ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
      ∃ m : Fin 17,
        let e := ((Finset.range m.val).filter (fun i => collatzStep^[i] r.val % 2 = 0)).card
        let o := ((Finset.range m.val).filter (fun i => collatzStep^[i] r.val % 2 = 1)).card
        e ≤ 10 ∧ 3001 ^ o < 2 ^ e * 1000 ^ o := by
    decide +kernel
  obtain ⟨m, hm⟩ := cert ⟨r, hr⟩ hc hs
  exact ⟨m.val, by have := m.isLt; omega, hm⟩