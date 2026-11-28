import OMAStatements.S_oeis_a113610

open OMA.S_oeis_a113610

private theorem prime_at {n p : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = n - 1) :
    prime n = p := by
  rw [prime, ← hc, Nat.nth_count hp]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a113610.main) := by
  intro h
  have p₁₂ : prime 12 = 37 := prime_at (by decide) (by decide +kernel)
  have p₁₃ : prime 13 = 41 := prime_at (by decide) (by decide +kernel)
  have p₁₄ : prime 14 = 43 := prime_at (by decide) (by decide +kernel)
  have p₁₅ : prime 15 = 47 := prime_at (by decide) (by decide +kernel)
  have a₁₂ : a 12 = 27 := by
    rw [a, p₁₂, p₁₃]
    decide +kernel
  have a₁₃ : a 13 = 6 := by
    rw [a, p₁₃, p₁₄]
    decide +kernel
  have a₁₄ : a 14 = 27 := by
    rw [a, p₁₄, p₁₅]
    decide +kernel
  have hf := h 12 (by decide)
    (show a 13 < a 12 by rw [a₁₃, a₁₂]; decide)
    (show a 13 < a 14 by rw [a₁₃, a₁₄]; decide)
  change prime 13 = prime 12 + 2 at hf
  rw [p₁₃, p₁₂] at hf
  omega