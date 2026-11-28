import FormalConjectures.ErdosProblems.«939»

lemma OMA.F {k a b : ℕ} (h : a ∣ b) : k.Full (a * b ^ k) := fun p hp => by
  have := Nat.mem_primeFactors.1 hp
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ((this.1.dvd_mul.1 this.2.1).elim (·.trans h)
    this.1.dvd_of_dvd_pow) k) a

theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.eight := by
  refine ⟨{1 * (1681 ^ 8 - 1680 ^ 8) ^ 8, 16 * (1681 ^ 7 * 1680) ^ 8, 42 * (1681 ^ 5 * 1680 ^ 3) ^ 8,
    70 * (1681 ^ 5 * 1680 ^ 3) ^ 8, 112 * (1681 ^ 3 * 1680 ^ 5) ^ 8, 16 * (1681 * 1680 ^ 7) ^ 8}, by decide, by decide, ?_, ?_⟩
  · convert OMA.F (one_dvd (1681 ^ 8 + 1680 ^ 8)) using 1
    decide
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro n (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, OMA.F (by norm_num)⟩
