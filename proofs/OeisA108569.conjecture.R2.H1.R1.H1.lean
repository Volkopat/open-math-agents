import OMAReductions.R_OeisA108569_conjecture_R2_H1_R1

-- Step OeisA108569.conjecture.R2.H1.R1.H1: hypothesis H1 of reduction OeisA108569.conjecture.R2.H1.R1
-- Credit: @JamesSlash. With m = p + phi p = 2 p - 1 (odd), phi p = phi m means 2 phi m = m - 1. Euler's product
-- phi m * prod q = m * prod (q - 1) over the (odd, so at least 3) prime factors q of m rules this out:
-- one prime factor q gives (p - 1) q = (2 p - 1)(q - 1), i.e. p (q - 2) + 1 = 0; two prime factors q, r give
-- p ((q - 2)(r - 2) - 2) + q + r - 1 = 0 with (q - 2)(r - 2) >= 2. No prime factor means m = 1.

theorem OMA.solution : OMA.R_OeisA108569_conjecture_R2_H1_R1.H1 := by
  intro p hp hodd hcard heq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  rw [Nat.totient_prime hp] at heq hcard
  have key := Nat.totient_mul_prod_primeFactors (p + (p - 1))
  rw [← heq] at key
  have hmodd : ¬ 2 ∣ p + (p - 1) := by omega
  have hq3 : ∀ q ∈ (p + (p - 1)).primeFactors, 3 ≤ q := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact hmodd hqd
    have := hqp.two_le
    omega
  obtain h | h | h : (p + (p - 1)).primeFactors.card = 0 ∨ (p + (p - 1)).primeFactors.card = 1 ∨
      (p + (p - 1)).primeFactors.card = 2 := by omega
  · rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h
    omega
  · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h
    have q3 := hq3 q (by rw [hq]; exact Finset.mem_singleton_self q)
    rw [hq, Finset.prod_singleton, Finset.prod_singleton] at key
    have h1 : (p - 1 : ℕ) = (p : ℤ) - 1 := by push_cast [show 1 ≤ p by omega]; ring
    have h2 : ((p + (p - 1) : ℕ) : ℤ) = 2 * (p : ℤ) - 1 := by push_cast [show 1 ≤ p by omega]; ring
    have h3 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by push_cast [show 1 ≤ q by omega]; ring
    have hz : (((p - 1) * q : ℕ) : ℤ) = (((p + (p - 1)) * (q - 1) : ℕ) : ℤ) := by rw [key]
    push_cast [show 1 ≤ p by omega, show 1 ≤ q by omega] at hz
    have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have hq3' : (3 : ℤ) ≤ q := by exact_mod_cast q3
    nlinarith
  · obtain ⟨q, r, hqr, hqrs⟩ := Finset.card_eq_two.mp h
    have q3 := hq3 q (by rw [hqrs]; simp)
    have r3 := hq3 r (by rw [hqrs]; simp)
    rw [hqrs, Finset.prod_pair hqr, Finset.prod_pair hqr] at key
    have hz : (((p - 1) * (q * r) : ℕ) : ℤ) = (((p + (p - 1)) * ((q - 1) * (r - 1)) : ℕ) : ℤ) := by
      rw [key]
    push_cast [show 1 ≤ p by omega, show 1 ≤ q by omega, show 1 ≤ r by omega] at hz
    have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have hq3' : (3 : ℤ) ≤ q := by exact_mod_cast q3
    have hr3' : (3 : ℤ) ≤ r := by exact_mod_cast r3
    have hqr' : (q : ℤ) ≠ r := by exact_mod_cast hqr
    have hprod : (2 : ℤ) ≤ ((q : ℤ) - 2) * ((r : ℤ) - 2) := by
      rcases lt_or_gt_of_ne hqr' with hlt | hlt
      · nlinarith
      · nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hprod (by linarith : (0 : ℤ) ≤ p)]
