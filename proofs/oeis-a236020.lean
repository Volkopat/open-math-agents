import OMAStatements.S_oeis_a236020

-- Credit: @tjgksruf9801 (shorter proof). 14 and 15 have the same divisor sum 24 and the same
-- number of divisors 4, so kVal 14 = kVal 15.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a236020.main) := fun h =>
  absurd (h 14 15 (by decide) (by decide) (by
    unfold OMA.S_oeis_a236020.kVal
    rw [show ∑ d ∈ (14 : ℕ).divisors, d = ∑ d ∈ (15 : ℕ).divisors, d by decide +kernel,
      show (14 : ℕ).divisors.card = (15 : ℕ).divisors.card by decide +kernel])) (by decide)
