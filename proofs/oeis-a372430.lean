import OMAStatements.S_oeis_a372430

namespace OMA.S_oeis_a372430




/-- The comment's conjecture. -/
def Conjecture : Prop := ∀ k : ℕ, 0 < k → binIdx k ⊆ primeIdx k → k = 4100

/-- The counterexample. -/
def k₀ : ℕ := 2 ^ 87 + 2 ^ 49

theorem count229 : Nat.count Nat.Prime 229 = 49 := by
  rw [Nat.count_eq_card_filter_range]
  decide +kernel

theorem count457 : Nat.count Nat.Prime 457 = 87 := by
  rw [Nat.count_eq_card_filter_range]
  decide +kernel

theorem prime_50 : prime 50 = 229 := by
  show Nat.nth Nat.Prime 49 = 229
  rw [← count229]
  exact Nat.nth_count (by norm_num)

theorem prime_88 : prime 88 = 457 := by
  show Nat.nth Nat.Prime 87 = 457
  rw [← count457]
  exact Nat.nth_count (by norm_num)

/-- The 1 bits of k₀ are bits 49 and 87 (0-based), that is, binary indices 50 and 88. -/
theorem testBit_k₀ (i : ℕ) (h : k₀.testBit i = true) : i = 49 ∨ i = 87 := by
  rcases Nat.lt_or_ge i 88 with hi | hi
  · have key : ∀ j < 88, k₀.testBit j = true → j = 49 ∨ j = 87 := by decide +kernel
    exact key i hi h
  · have hlt : k₀ < 2 ^ i :=
      lt_of_lt_of_le (by norm_num [k₀]) (Nat.pow_le_pow_right (by norm_num) hi)
    rw [Nat.testBit_lt_two_pow hlt] at h
    exact absurd h (by simp)

theorem binIdx_k₀ : binIdx k₀ ⊆ primeIdx k₀ := by
  rintro i ⟨hi1, hbit⟩
  refine ⟨hi1, ?_⟩
  rcases testBit_k₀ (i - 1) hbit with h | h
  · obtain rfl : i = 50 := by omega
    rw [prime_50]
    norm_num [k₀]
  · obtain rfl : i = 88 := by omega
    rw [prime_88]
    norm_num [k₀]

theorem disproof : ¬ Conjecture := by
  intro h
  have := h k₀ (by norm_num [k₀]) binIdx_k₀
  norm_num [k₀] at this

end OMA.S_oeis_a372430

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a372430.main) :=
  OMA.S_oeis_a372430.disproof
