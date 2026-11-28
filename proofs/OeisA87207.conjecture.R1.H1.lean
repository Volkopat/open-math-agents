import OMAReductions.R_OeisA87207_conjecture_R1

/-!
# Step H1 of the reduction OeisA87207.conjecture.R1

For `e ≥ 1` the prime factors of `2 ^ e * c` are those of `2 * c`, so `a (2 ^ e * c) = a (2 * c)`.
The orbits of `c` and `2 * c` for the six listed `c` reach `0` and are checked by the kernel.
-/

open OeisA87207

namespace OMA.H87207

theorem a_two_pow_mul (e c : ℕ) (he : 1 ≤ e) (hc : c ≠ 0) : a (2 ^ e * c) = a (2 * c) := by
  unfold a
  rw [Nat.support_factorization, Nat.support_factorization,
    Nat.primeFactors_mul (by positivity) hc, Nat.primeFactors_mul (by norm_num) hc,
    Nat.primeFactors_pow _ (by omega)]

end OMA.H87207

theorem OMA.solution : OMA.R_OeisA87207_conjecture_R1.H1 := by
  intro e c hc
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp only [pow_zero, one_mul]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨3, by decide +kernel⟩
    · exact ⟨3, by decide +kernel⟩
    · exact ⟨3, by decide +kernel⟩
    · exact ⟨3, by decide +kernel⟩
  · have hc0 : c ≠ 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      omega
    have key : ∃ k, (a^[k]) (a (2 * c)) = 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by decide +kernel⟩
      · exact ⟨1, by decide +kernel⟩
      · exact ⟨3, by decide +kernel⟩
      · exact ⟨3, by decide +kernel⟩
      · exact ⟨3, by decide +kernel⟩
      · exact ⟨6, by decide +kernel⟩
    obtain ⟨k, hk⟩ := key
    refine ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply, OMA.H87207.a_two_pow_mul e c he hc0]
    exact hk
