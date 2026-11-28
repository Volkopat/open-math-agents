import OMAReductions.R_Erdos945_erdos_945_variants_constant_R1

-- Step Erdos945.erdos_945.variants.constant.R1.H2: hypothesis H2 of reduction Erdos945.erdos_945.variants.constant.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_Erdos945_erdos_945_variants_constant_R1.H2 := by
  intro n hn
  have hn0 : n ≠ 0 := hn.ne_zero
  show n.divisors.card = _
  rw [Nat.card_divisors hn0, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h1 := hn.natFactorization_le_one p
  have h2 : 0 < n.factorization p :=
    Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn0
      (Nat.dvd_of_mem_primeFactors hp)
  omega
