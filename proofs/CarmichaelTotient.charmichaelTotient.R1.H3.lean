import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

open Nat in
theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H3 := by
  have key (k : ℕ) (h6 : 42 ∣ k) (h7 : ¬ 43 ∣ k) : φ (42 * k) = φ (43 * k) := by
    rw [show 42 * k = 2 * (3 * (7 * k)) by ring, totient_mul_of_prime_of_dvd prime_two (by omega),
      totient_mul_of_prime_of_dvd prime_three (by omega),
      totient_mul_of_prime_of_dvd (by norm_num : (7).Prime) (by omega),
      totient_mul ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7), totient_prime (p := 43) (by norm_num)]
    omega
  intro n h36 h49 h
  by_cases h43 : 43 ∣ n
  · obtain ⟨j, rfl⟩ := h43
    exact ⟨42 * j, by omega, key j (by omega) (by omega)⟩
  · obtain ⟨k, rfl⟩ : 42 ∣ n := by omega
    exact ⟨43 * k, by omega, (key k (by omega) (by omega)).symm⟩
