import OMAReductions.R_Erdos945_erdos_945_R1

/-! The prime factorization of a squarefree integer has only exponents one. -/
-- Credit: @marcusbuffett
theorem OMA.solution : OMA.R_Erdos945_erdos_945_R1.H2 := by
  intro n hn
  rw [Erdos945.τ, Nat.card_divisors hn.ne_zero]
  apply Finset.prod_eq_pow_card
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)]
