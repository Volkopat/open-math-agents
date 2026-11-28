import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1

-- Step PerfectNumbers.odd_perfect_number_conjecture.R1.H1.R1.H1: hypothesis H1 of reduction PerfectNumbers.odd_perfect_number_conjecture.R1.H1.R1
-- Credit: @sukhman31
-- H1 := ∀ n : ℕ, Nat.Perfect n → Odd n → n.primeFactors.card ≤ 2 → Nat.minFac n ≠ 3

private lemma sum_divisors_prime_pow_bound {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p - 1) * (∑ d ∈ (p ^ k).divisors, d) + 1 = p ^ (k + 1) := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  induction k with
  | zero =>
    simp only [Nat.reduceAdd, Finset.sum_range_one, pow_zero, mul_one, pow_one]
    have := hp.two_le
    omega
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add]
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hstep : (p - 1) * p ^ (k + 1) + p ^ (k + 1) = p ^ (k + 1 + 1) := by
      calc
        (p - 1) * p ^ (k + 1) + p ^ (k + 1) = (p - 1 + 1) * p ^ (k + 1) := by ring
        _ = p * p ^ (k + 1) := by rw [Nat.sub_add_cancel hp1]
        _ = p ^ (k + 1 + 1) := by ring
    omega

private lemma sum_divisors_prime_pow_lt {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p - 1) * (∑ d ∈ (p ^ k).divisors, d) < p * p ^ k := by
  have h := sum_divisors_prime_pow_bound hp k
  rw [pow_succ'] at h
  omega

private lemma sum_divisors_mul_coprime {a b : ℕ} (hab : a.Coprime b) :
    (∑ d ∈ (a * b).divisors, d) = (∑ d ∈ a.divisors, d) * (∑ d ∈ b.divisors, d) := by
  simpa [ArithmeticFunction.sigma_one_apply] using
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hab

private lemma sum_divisors_eq_two_mul_of_perfect {n : ℕ} (hn : Nat.Perfect n) :
    (∑ d ∈ n.divisors, d) = 2 * n := by
  have hprop : ∑ d ∈ n.properDivisors, d = n := hn.1
  have hsum : ∑ d ∈ n.divisors, d = ∑ d ∈ n.properDivisors, d + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  omega

private lemma prime_ge_three_of_mem_odd {n p : ℕ} (hodd : Odd n) (hp : p ∈ n.primeFactors) :
    p.Prime ∧ 3 ≤ p ∧ p % 2 = 1 := by
  have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hne2 : p ≠ 2 := by
    intro h2
    subst h2
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm⟩ := hdvd
    omega
  have h2le : 2 ≤ p := hpr.two_le
  have hodd_p : Odd p := hpr.odd_of_ne_two hne2
  obtain ⟨k, hk⟩ := hodd_p
  exact ⟨hpr, by omega, by omega⟩

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1.H1 := by
  intro n hperf hodd hcard _
  have hn_pos : 0 < n := hperf.2
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hdiv : (∑ d ∈ n.divisors, d) = 2 * n := sum_divisors_eq_two_mul_of_perfect hperf
  have hprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn_ne
  have hcases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · have hemp : n.primeFactors = ∅ := Finset.card_eq_zero.mp h0
    rw [hemp, Finset.prod_empty] at hprod
    subst hprod
    simp at hdiv
  · obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp h1
    have hp_mem : p ∈ n.primeFactors := by rw [hp_eq]; exact Finset.mem_singleton_self p
    obtain ⟨hpr, hp3, _⟩ := prime_ge_three_of_mem_odd hodd hp_mem
    rw [hp_eq, Finset.prod_singleton] at hprod
    have hlt := sum_divisors_prime_pow_lt hpr (n.factorization p)
    rw [hprod, hdiv] at hlt
    zify [show 1 ≤ p by omega] at hlt
    nlinarith
  · obtain ⟨p, q, hpq, hpq_eq⟩ := Finset.card_eq_two.mp h2
    have hp_mem : p ∈ n.primeFactors := by rw [hpq_eq]; simp
    have hq_mem : q ∈ n.primeFactors := by rw [hpq_eq]; simp
    obtain ⟨hpr, hp3, hp_mod⟩ := prime_ge_three_of_mem_odd hodd hp_mem
    obtain ⟨hqr, hq3, hq_mod⟩ := prime_ge_three_of_mem_odd hodd hq_mem
    rw [hpq_eq, Finset.prod_pair hpq] at hprod
    have hcop : (p ^ n.factorization p).Coprime (q ^ n.factorization q) :=
      ((Nat.coprime_primes hpr hqr).mpr hpq).pow _ _
    have hdiv_mul := sum_divisors_mul_coprime hcop
    rw [hprod] at hdiv_mul
    have hlt_p := sum_divisors_prime_pow_lt hpr (n.factorization p)
    have hlt_q := sum_divisors_prime_pow_lt hqr (n.factorization q)
    have hlt_prod :
        ((p - 1) * ∑ d ∈ (p ^ n.factorization p).divisors, d) *
        ((q - 1) * ∑ d ∈ (q ^ n.factorization q).divisors, d) <
        (p * p ^ n.factorization p) * (q * q ^ n.factorization q) :=
      Nat.mul_lt_mul_of_lt_of_lt hlt_p hlt_q
    have hlhs :
        ((p - 1) * ∑ d ∈ (p ^ n.factorization p).divisors, d) *
        ((q - 1) * ∑ d ∈ (q ^ n.factorization q).divisors, d) =
        (p - 1) * (q - 1) * (2 * n) := by
      calc
        ((p - 1) * ∑ d ∈ (p ^ n.factorization p).divisors, d) *
            ((q - 1) * ∑ d ∈ (q ^ n.factorization q).divisors, d)
            = (p - 1) * (q - 1) *
              ((∑ d ∈ (p ^ n.factorization p).divisors, d) *
               (∑ d ∈ (q ^ n.factorization q).divisors, d)) := by ring
        _ = (p - 1) * (q - 1) * (2 * n) := by rw [← hdiv_mul, hdiv]
    have hrhs :
        (p * p ^ n.factorization p) * (q * q ^ n.factorization q) = p * q * n := by
      calc
        (p * p ^ n.factorization p) * (q * q ^ n.factorization q)
            = p * q * (p ^ n.factorization p * q ^ n.factorization q) := by ring
        _ = p * q * n := by rw [hprod]
    rw [hlhs, hrhs] at hlt_prod
    have hge : p * q ≤ (p - 1) * (q - 1) * 2 := by
      have h5 : (3 ≤ p ∧ 5 ≤ q) ∨ (5 ≤ p ∧ 3 ≤ q) := by omega
      rcases h5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · zify [show 1 ≤ p by omega, show 1 ≤ q by omega]
        nlinarith
      · zify [show 1 ≤ p by omega, show 1 ≤ q by omega]
        nlinarith
    have hmul : p * q * n ≤ (p - 1) * (q - 1) * (2 * n) := by
      calc
        p * q * n ≤ (p - 1) * (q - 1) * 2 * n := Nat.mul_le_mul_right n hge
        _ = (p - 1) * (q - 1) * (2 * n) := by ring
    omega
