import OMAReductions.R_Erdos399_erdos_399_variants_sum_two_squares_R1

-- Original proof: @JamesSlash. Finite-search proof: @menelikbaye-digitalmethod.
-- Both n and a witnessing prime lie in the range 0 through 100.
set_option maxRecDepth 4096 in
theorem OMA.solution : OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H1 := by
  intro n hn hmax
  have cover : ∀ k : Fin 101, 7 ≤ k.val →
      ∃ q : Fin 101, q.val.Prime ∧ q.val % 4 = 3 ∧ k.val < 2*q.val ∧ q.val ≤ k.val := by
    decide +kernel
  obtain ⟨q, hq⟩ := cover ⟨n, by omega⟩ hn
  exact ⟨q.val, hq⟩
