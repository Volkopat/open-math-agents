import OMAReductions.R_oeis_a122036_R1
import Mathlib

/-! An odd `n` with at most two distinct prime factors is deficient: with `σ` multiplicative and
`(p - 1) σ(p^e) < p^(e+1)`, `σ(n) / n < ∏ p / (p - 1) ≤ (3/2)(5/4) < 2` (two distinct odd primes
satisfy `(p - 2)(q - 2) ≥ 3`). -/

open Finset

namespace OMA.Step_oeis_a122036_R1_H1

/-- `(p - 1) (1 + p + ⋯ + p^k) + 1 = p^(k+1)`, written with `p = a + 1`. -/
theorem geom (a k : ℕ) : a * ∑ i ∈ range (k + 1), (a + 1) ^ i + 1 = (a + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih]
    ring

/-- For a prime `p = a + 1`: `a * σ(p^e) + 1 = p * p^e`. -/
theorem sigma_pp {p a e : ℕ} (hp : p.Prime) (ha : p = a + 1) :
    a * ∑ d ∈ (p ^ e).divisors, d + 1 = p * p ^ e := by
  rw [Nat.sum_divisors_prime_pow hp, ha, geom, pow_succ, mul_comm]

theorem deficient (n : ℕ) (hodd : Odd n) (hcard : n.primeFactors.card ≤ 2) :
    ∑ d ∈ n.properDivisors, d < n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have hσ : ∑ d ∈ n.divisors, d =
      ∏ p ∈ n.primeFactors, ∑ d ∈ (p ^ n.factorization p).divisors, d := by
    have := ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization
      (ArithmeticFunction.sigma 1) hn0
    simp only [ArithmeticFunction.sigma_one_apply] at this
    rw [this, Finsupp.prod, Nat.support_factorization]
  have hN : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod, Nat.support_factorization]
  -- every prime factor is an odd prime, so at least 3
  have hodd_p : ∀ p ∈ n.primeFactors, 3 ≤ p ∧ Odd p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpo : Odd p := Odd.of_dvd_nat hodd hpd
    refine ⟨?_, hpo⟩
    rcases hpp.eq_two_or_odd' with h | h
    · subst h; exact absurd hpo (by decide)
    · have := hpp.two_le
      rcases Nat.lt_or_ge p 3 with h3 | h3
      · interval_cases p; exact absurd hpo (by decide)
      · exact h3
  have key : ∑ d ∈ n.divisors, d < 2 * n := by
    rcases Nat.lt_or_ge n.primeFactors.card 3 with _ | h
    swap; · omega
    interval_cases hc : n.primeFactors.card
    · -- n = 1
      rw [Finset.card_eq_zero] at hc
      rw [hσ, hN, hc]; simp
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
      have hpm : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
      obtain ⟨h3, -⟩ := hodd_p p hpm
      have hpp := Nat.prime_of_mem_primeFactors hpm
      obtain ⟨a, ha⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
      have hs := sigma_pp (e := n.factorization p) hpp ha
      rw [hσ, hp, Finset.prod_singleton]
      conv_rhs => rw [hN, hp, Finset.prod_singleton]
      set s := ∑ d ∈ (p ^ n.factorization p).divisors, d
      set P := p ^ n.factorization p
      subst ha
      nlinarith
    · obtain ⟨p, q, hpq, hpqs⟩ := Finset.card_eq_two.mp hc
      have hpm : p ∈ n.primeFactors := by rw [hpqs]; simp
      have hqm : q ∈ n.primeFactors := by rw [hpqs]; simp
      obtain ⟨hp3, hpo⟩ := hodd_p p hpm
      obtain ⟨hq3, hqo⟩ := hodd_p q hqm
      obtain ⟨a, ha⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
      have hs := sigma_pp (e := n.factorization p) (Nat.prime_of_mem_primeFactors hpm) ha
      have ht := sigma_pp (e := n.factorization q) (Nat.prime_of_mem_primeFactors hqm) hb
      rw [hσ, hpqs, Finset.prod_pair hpq]
      conv_rhs => rw [hN, hpqs, Finset.prod_pair hpq]
      set s := ∑ d ∈ (p ^ n.factorization p).divisors, d
      set t := ∑ d ∈ (q ^ n.factorization q).divisors, d
      set P := p ^ n.factorization p
      set Q := q ^ n.factorization q
      -- one of the two odd primes is at least 5, so (p - 2)(q - 2) ≥ 3
      have hab : 3 ≤ (a - 1) * (b - 1) := by
        rcases Nat.lt_or_gt_of_ne hpq with h | h
        · have : 5 ≤ q := by
            obtain ⟨i, hi⟩ := hpo; obtain ⟨j, hj⟩ := hqo; omega
          have h1 : 1 ≤ a - 1 := by omega
          have h2 : 3 ≤ b - 1 := by omega
          nlinarith
        · have : 5 ≤ p := by
            obtain ⟨i, hi⟩ := hpo; obtain ⟨j, hj⟩ := hqo; omega
          have h1 : 3 ≤ a - 1 := by omega
          have h2 : 1 ≤ b - 1 := by omega
          nlinarith
      -- a s < p P,  b t < q Q  ⇒  a b s t < p q P Q ≤ 2 a b P Q
      have hpq2 : (a + 1) * (b + 1) ≤ 2 * (a * b) := by
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hab
        nlinarith
      have h1 : a * s < p * P := by omega
      have h2 : b * t < q * Q := by omega
      have h12 : (a * s) * (b * t) < (p * P) * (q * Q) :=
        Nat.mul_lt_mul'' h1 h2
      have hab0 : 0 < a * b := by
        have : 0 < a := by omega
        have : 0 < b := by omega
        positivity
      have h3 : (a * b) * (s * t) < (a * b) * (2 * (P * Q)) := by
        calc (a * b) * (s * t) = (a * s) * (b * t) := by ring
          _ < (p * P) * (q * Q) := h12
          _ = ((a + 1) * (b + 1)) * (P * Q) := by rw [ha, hb]; ring
          _ ≤ (2 * (a * b)) * (P * Q) := Nat.mul_le_mul_right _ hpq2
          _ = (a * b) * (2 * (P * Q)) := by ring
      exact Nat.lt_of_mul_lt_mul_left h3
  have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)
  omega

end OMA.Step_oeis_a122036_R1_H1

theorem OMA.solution : OMA.R_oeis_a122036_R1.H1 := OMA.Step_oeis_a122036_R1_H1.deficient
