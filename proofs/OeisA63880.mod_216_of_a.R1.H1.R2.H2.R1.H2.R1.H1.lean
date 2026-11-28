import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1_H2_R1

-- Step OeisA63880.mod_216_of_a.R1.H1.R2.H2.R1.H2.R1.H1: hypothesis H1 of reduction OeisA63880.mod_216_of_a.R1.H1.R2.H2.R1.H2.R1
-- Credit: @luciusacarr
-- H1 := ∀ d : ℕ, Odd d →   (∀ q : ℕ, q.Prime → q ∣ d → 2 ≤ d.factorization q) →   (∀ q : ℕ, q.Prime → q ∣ d → Even (d.factorization q)) → ¬ OeisA63880.A d

/-! If every exponent of the odd number `d` is even, then `τ(d) = ∏ (e_p + 1)` is odd, and since
every divisor of `d` is odd, `σ(d) ≡ τ(d) ≡ 1 (mod 2)`. But `A d` requires
`σ(d) = 2 · usigma(d)`, which is even. -/

open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1_H2_R1.H1 := by
  intro d hodd _ heven hA
  obtain ⟨hpos, hσ⟩ := hA
  have hd0 : d ≠ 0 := by omega
  -- τ(d) is odd
  have hτ : d.divisors.card % 2 = 1 := by
    rw [Nat.card_divisors hd0, Finset.prod_nat_mod]
    have : ∀ p ∈ d.primeFactors, (d.factorization p + 1) % 2 = 1 := by
      intro p hp
      have := heven p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      obtain ⟨k, hk⟩ := this
      omega
    rw [Finset.prod_congr rfl this]
    simp
  -- σ(d) ≡ τ(d) mod 2
  have hs : (σ 1 d) % 2 = 1 := by
    rw [ArithmeticFunction.sigma_one_apply, Finset.sum_nat_mod]
    have : ∀ x ∈ d.divisors, x % 2 = 1 := by
      intro x hx
      have hxd := Nat.dvd_of_mem_divisors hx
      have : Odd x := Odd.of_dvd_nat hodd hxd
      exact Nat.odd_iff.mp this
    rw [Finset.sum_congr rfl this]
    simp [hτ]
  omega
