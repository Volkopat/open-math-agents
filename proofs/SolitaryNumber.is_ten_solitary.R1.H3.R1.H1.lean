import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1_H3_R1

-- An odd square m with 10 sigma(m) = 18 m (abundancy 9/5, a friend of 10) has at least three distinct prime
-- factors. Original Lean proof of an elementary case. 5 divides m. A power of 5 has abundancy below 5/4. For
-- m = 5^e q^f with q >= 7 the abundancy is below (5/4)(7/6) < 9/5. For q = 3 the exponent e is even because m is
-- a square, so sigma(5^e) is 1 mod 3 and 1 mod 5, hence coprime to 9 * 5^e * 3^f, which it divides: impossible.
-- An elementary case, not progress on the question whether 10 is solitary.

namespace OMA.Solitary3

open ArithmeticFunction Finset

lemma geom' (c : ℕ) : ∀ i : ℕ, (∑ k ∈ range (i + 1), (c + 1) ^ k) * c + 1 = (c + 1) ^ (i + 1) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have e : (c + 1) ^ (i + 1 + 1) = (c + 1) ^ (i + 1) * (c + 1) := pow_succ _ _
    rw [Finset.sum_range_succ, e]
    nlinarith [ih]

lemma geom (p : ℕ) (hp : 1 ≤ p) (i : ℕ) : (∑ k ∈ range (i + 1), p ^ k) * (p - 1) + 1 = p ^ (i + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
  simpa using geom' c i

/-- `S p a = 1 + p + ... + p^a`, the divisor sum of `p^a`. -/
def S (p a : ℕ) : ℕ := ∑ i ∈ range (a + 1), p ^ i

lemma S_succ (p a : ℕ) : S p (a + 1) = p * S p a + 1 := by
  unfold S
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ']

lemma S_upper (p a : ℕ) (hp : 1 ≤ p) : S p a * (p - 1) + 1 = p * p ^ a := by
  have h := geom p hp a
  rw [pow_succ'] at h
  exact h

lemma sigma_pp (p a : ℕ) (hp : p.Prime) : sigma 1 (p ^ a) = S p a :=
  sigma_one_apply_prime_pow hp

lemma S5_mod_five (e : ℕ) : S 5 e % 5 = 1 := by
  induction e with
  | zero => simp [S]
  | succ e ih =>
    rw [S_succ]
    omega

lemma S5_mod_three : ∀ k : ℕ, S 5 (2 * k) % 3 = 1 := by
  intro k
  induction k with
  | zero => simp [S]
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e, S_succ, S_succ]
    omega

/-- An odd square `m` with `10 σ(m) = 18 m` has at least three distinct prime factors. -/
theorem few_primes (m : ℕ) (hodd : Odd m) (hsq : IsSquare m) (hc : m.primeFactors.card ≤ 2) :
    sigma 1 m * 10 ≠ 18 * m := by
  intro hs
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hodd
  have hm0 : m ≠ 0 := by omega
  have p5 : Nat.Prime 5 := by norm_num
  have h5 : 5 ∣ m := by omega
  have h5mem : 5 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨p5, h5, hm0⟩
  obtain ⟨r, rfl⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hm0
  -- exponents in a square are even
  have heven : ∀ p : ℕ, (r * r).factorization p % 2 = 0 := by
    intro p
    rw [Nat.factorization_mul hr0 hr0]
    simp only [Finsupp.coe_add, Pi.add_apply]
    omega
  have hfac := Nat.prod_factorization_pow_eq_self hm0
  rw [Nat.prod_factorization_eq_prod_primeFactors] at hfac
  have hcard : (r * r).primeFactors.card = 1 ∨ (r * r).primeFactors.card = 2 := by
    have h1 : 0 < (r * r).primeFactors.card := Finset.card_pos.mpr ⟨5, h5mem⟩
    omega
  have he0 : 0 < (r * r).factorization 5 := Nat.Prime.factorization_pos_of_dvd p5 hm0 h5
  rcases hcard with h1 | h2
  · -- a power of 5 is deficient
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have hx5 : x = 5 := by
      rw [hx, Finset.mem_singleton] at h5mem
      exact h5mem.symm
    rw [hx, hx5, Finset.prod_singleton] at hfac
    generalize (r * r).factorization 5 = e at hfac he0
    rw [← hfac, sigma_pp 5 e p5] at hs
    have hu := S_upper 5 e (by norm_num)
    omega
  · -- two primes: 5 and q
    have hcard1 : ((r * r).primeFactors.erase 5).card = 1 := by
      rw [Finset.card_erase_of_mem h5mem, h2]
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard1
    have hqmem : q ∈ (r * r).primeFactors.erase 5 := by rw [hq]; exact Finset.mem_singleton_self q
    have hq5 : q ≠ 5 := Finset.ne_of_mem_erase hqmem
    have hqmem' := Finset.mem_of_mem_erase hqmem
    have hqp := Nat.prime_of_mem_primeFactors hqmem'
    have hqd := Nat.dvd_of_mem_primeFactors hqmem'
    have hq2 : q ≠ 2 := by
      rintro rfl
      omega
    have hpf : (r * r).primeFactors = {5, q} := by
      rw [← Finset.insert_erase h5mem, hq]
    rw [hpf, Finset.prod_insert (by simp [hq5.symm]), Finset.prod_singleton] at hfac
    have hf0 : 0 < (r * r).factorization q := Nat.Prime.factorization_pos_of_dvd hqp hm0 hqd
    have he2 := heven 5
    generalize (r * r).factorization 5 = e at hfac he0 he2
    generalize (r * r).factorization q = f at hfac hf0
    have c5q : Nat.Coprime 5 q := (Nat.coprime_primes p5 hqp).mpr hq5.symm
    have hsig : S 5 e * S q f * 10 = 18 * (5 ^ e * q ^ f) := by
      rw [← sigma_pp 5 e p5, ← sigma_pp q f hqp,
        ← isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow e f c5q), hfac]
      exact hs
    have hu5 := S_upper 5 e (by norm_num)
    have huq := S_upper q f hqp.one_lt.le
    by_cases hq3 : q = 3
    · -- q = 3: the divisor sum of 5^e is coprime to 15 and would have to divide a 3-smooth number
      subst hq3
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
      have hm3 := S5_mod_three k
      have hm5 := S5_mod_five (2 * k)
      have hcop3 : Nat.Coprime (S 5 (2 * k)) 3 := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
        omega
      have hcop5 : Nat.Coprime (S 5 (2 * k)) 5 := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd p5]
        omega
      have hcop : Nat.Coprime (S 5 (2 * k)) (9 * (5 ^ (2 * k) * 3 ^ f)) := by
        apply Nat.Coprime.mul_right
        · exact (hcop3.pow_right 2 : Nat.Coprime (S 5 (2 * k)) (3 ^ 2))
        · exact Nat.Coprime.mul_right (hcop5.pow_right _) (hcop3.pow_right _)
      have hdvd : S 5 (2 * k) ∣ 9 * (5 ^ (2 * k) * 3 ^ f) := by
        refine ⟨5 * S 3 f, ?_⟩
        have e1 : S 5 (2 * k) * S 3 f * 10 = 2 * (S 5 (2 * k) * (5 * S 3 f)) := by ring
        have e2 : 18 * (5 ^ (2 * k) * 3 ^ f) = 2 * (9 * (5 ^ (2 * k) * 3 ^ f)) := by ring
        rw [e1, e2] at hsig
        omega
      have hone := Nat.Coprime.eq_one_of_dvd hcop hdvd
      have hk : 1 ≤ k := by omega
      have hpow : 5 ≤ 5 ^ (2 * k) := by
        calc 5 = 5 ^ 1 := by norm_num
          _ ≤ 5 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hone] at hu5
      omega
    · -- q ≥ 7: deficient
      have hq7 : 7 ≤ q := by
        have h2 := hqp.two_le
        have hodd' : q % 2 = 1 := by
          rcases hqp.eq_two_or_odd with h | h
          · exact absurd h hq2
          · exact h
        have hq4 : q ≠ 4 := by rintro rfl; omega
        have hq6 : q ≠ 6 := by rintro rfl; omega
        omega
      obtain ⟨d, rfl⟩ : ∃ d, q = d + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at huq
      -- S5 * 4 < 5 * 5^e and Sq * d < (d + 1) * q^f
      have h1 : S 5 e * 4 < 5 * 5 ^ e := by omega
      have h2 : S (d + 1) f * d < (d + 1) * (d + 1) ^ f := by omega
      have h3 := Nat.mul_lt_mul'' h1 h2
      have e1 : S 5 e * 4 * (S (d + 1) f * d) = (S 5 e * S (d + 1) f) * (4 * d) := by ring
      have e2 : 5 * 5 ^ e * ((d + 1) * (d + 1) ^ f) = (5 ^ e * (d + 1) ^ f) * (5 * (d + 1)) := by ring
      rw [e1, e2] at h3
      -- 10 * (S5 Sq) = 18 * M and (S5 Sq) * 4d < M * 5(d+1), with 36 d ≥ 25 (d + 1) for d ≥ 6
      have hM : 0 < 5 ^ e * (d + 1) ^ f := by positivity
      nlinarith [hsig, h3, hM]

end OMA.Solitary3

theorem OMA.solution : OMA.R_SolitaryNumber_is_ten_solitary_R1_H3_R1.H1 := by
  intro m hodd hsq hc
  exact OMA.Solitary3.few_primes m hodd hsq hc
