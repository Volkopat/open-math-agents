import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H1_R1

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H1_R1.H2 :=
  fun _ _ _ _ _ _ _ ⟨p, a, _, b, c⟩ _ h => (h ⟨p, a, b, by omega, by omega, by omega, c⟩).elim
