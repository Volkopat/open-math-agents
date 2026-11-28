import OMAStatements.S_oeis_a309353

theorem OMA.solution : type_of% @OMA.S_oeis_a309353.main := by
  intro m k hm hS
  rcases k.eq_two_pow_or_exists_odd_prime_and_dvd with h | ⟨q, hq, hd, ho⟩
  · exact h
  have : q ∈ k.divisors := by
    rcases k with _|_ <;> simp_all
  rw [← hS, Finset.mem_image] at this
  obtain ⟨d, -, rfl⟩ := this
  exfalso
  rcases le_or_gt d 2 with h | h
  · interval_cases d <;> norm_num at hq
  · exact (Nat.not_even_iff_odd.2 ho) (Nat.totient_even h)
