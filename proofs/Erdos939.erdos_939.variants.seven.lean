import FormalConjectures.ErdosProblems.«939»

lemma OMA.F {k a b : ℕ} (h : a ∣ b) : k.Full (a * b ^ k) := fun p hp => by
  have := Nat.mem_primeFactors.1 hp
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ((this.1.dvd_mul.1 this.2.1).elim (·.trans h)
    this.1.dvd_of_dvd_pow) k) a

theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.seven := by
  refine ⟨{1 * (211 ^ 7 - 210 ^ 7) ^ 7, 14 * (211 ^ 6 * 210) ^ 7, 70 * (211 ^ 4 * 210 ^ 3) ^ 7,
    42 * (211 ^ 2 * 210 ^ 5) ^ 7, 2 * (210 ^ 7) ^ 7}, by decide, by decide, ?_, ?_⟩
  · convert OMA.F (one_dvd (211 ^ 7 + 210 ^ 7)) using 1
    decide
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro n (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, OMA.F (by norm_num)⟩
