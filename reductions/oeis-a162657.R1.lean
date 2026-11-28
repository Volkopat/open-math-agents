import OMAStatements.S_oeis_a162657

-- Reduction oeis-a162657.R1 of A162657: Least number m such that n is the denominator of sigma_{-1}(m), or zero if no such exists.
-- Credit: @notswizz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Proved here (no hypothesis needed): n = 1; prime powers n = p^a (m = n, since sigma(p^a) = 1 mod p);
-- and all squarefree semiprimes n = pq, p < q (argument from @Mapika, desk note 2026-11-28):
-- m = 18 for (2,3), otherwise m = p^(t+1) q with t = v_p(q+1); then sigma(m)/m = S c/(pq) with
-- S = 1 + p + ... + p^(t+1), c = (q+1)/p^t, and gcd(S c, pq) = 1. The only nontrivial point is
-- q not dividing S (lemma key): t = 0 forces (2,3); if q >= p^2 then q | S gives q | p^2 - c, impossible;
-- if q < p^2 then t <= 2, t = 2 forces (2,3), and t = 1 is ruled out by writing 1+p+p^2 = qk with p | k+1.
-- Remaining: H1 (at least three distinct prime factors) and H2 (p^a q^b with a + b >= 3).

namespace OMA.R_oeis_a162657_R1

theorem geomS (p T : ℕ) : ((∑ i ∈ Finset.range (T+2), p^i : ℕ) : ℤ) * ((p:ℤ) - 1) = (p:ℤ)^(T+2) - 1 := by
  push_cast
  exact geom_sum_mul (p:ℤ) (T+2)

theorem gen (p q T c : ℕ) (hp : p.Prime) (hq : q.Prime) (hT : 1 ≤ T) (hpq : p ^ 2 ≤ q)
    (hqc : q + 1 = p^T * c) (hpc : ¬ p ∣ c) : ¬ q ∣ ∑ i ∈ Finset.range (T+2), p^i := by
  intro hS
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have h1 : ((q:ℤ)) ∣ (p:ℤ)^(T+2) - 1 := by
    rw [← geomS]; exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hS) _
  have h2 : (q:ℤ) ∣ (p:ℤ)^2 - c := by
    have e : (c:ℤ) * ((p:ℤ)^(T+2) - 1) = (p:ℤ)^2 * ((q:ℤ) + 1) - c := by
      have : ((q:ℤ) + 1) = (p:ℤ)^T * c := by exact_mod_cast hqc
      rw [this]; ring
    have h3 : (q:ℤ) ∣ (p:ℤ)^2 * ((q:ℤ) + 1) - c := e ▸ Dvd.dvd.mul_left h1 _
    have h4 : (p:ℤ)^2 - c = ((p:ℤ)^2 * ((q:ℤ) + 1) - c) - (p:ℤ)^2 * q := by ring
    rw [h4]; exact dvd_sub h3 (Dvd.dvd.mul_left (dvd_refl _) _)
  have hpT : 2 ≤ p ^ T := le_trans hp2 (Nat.le_self_pow (by omega) p)
  have hc : c < q := by nlinarith
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hqc; simp at hqc
    · exact h
  have hz : (p:ℤ)^2 - c = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd h2
    have : ((p^2 : ℕ) : ℤ) ≤ q := by exact_mod_cast hpq
    push_cast at this
    have hc' : (c:ℤ) < q := by exact_mod_cast hc
    have hc0' : (0:ℤ) < c := by exact_mod_cast hc0
    have hp0 : (0:ℤ) ≤ (p:ℤ)^2 := by positivity
    rw [abs_lt]; constructor <;> linarith
  have : c = p^2 := by
    have : (c:ℤ) = (p:ℤ)^2 := by linarith
    exact_mod_cast this
  exact hpc (this ▸ dvd_pow_self p (by norm_num))

theorem key (p q t c : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hne : ¬ (p = 2 ∧ q = 3))
    (hqc : q + 1 = p^t * c) (hpc : ¬ p ∣ c) : ¬ q ∣ ∑ i ∈ Finset.range (t+2), p^i := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  rcases Nat.lt_or_ge q (p^2) with hlt | hge
  swap
  · rcases t with _ | t
    · intro ⟨k, hk⟩
      simp [Finset.sum_range_succ] at hk
      rcases k with _ | k
      · omega
      · nlinarith
    · exact gen p q (t+1) c hp hq (by omega) hge hqc hpc
  rcases t with _ | _ | _ | t
  · intro ⟨k, hk⟩
    simp [Finset.sum_range_succ] at hk
    -- hk : 1 + p = q * k
    have hk1 : k = 1 := by
      rcases k with _ | _ | k
      · omega
      · rfl
      · nlinarith
    subst hk1
    have hqp : q = p + 1 := by omega
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact hne ⟨h2, by omega⟩
    · rcases hq.eq_two_or_odd with h2 | hodd'
      · omega
      · omega
  · intro ⟨k, hk⟩
    simp [Finset.sum_range_succ] at hk
    -- hk : 1 + p + p^2 = q * k, hqc : q + 1 = p * c
    simp at hqc
    have hdiv : p ∣ k + 1 := by
      have e : 1 + p + p^2 + k = p * (c * k) := by nlinarith
      have : p ∣ 1 + p + p^2 + k := e ▸ dvd_mul_right p _
      have h' : 1 + p + p^2 + k = (k + 1) + p * (1 + p) := by ring
      rw [h'] at this
      exact (Nat.dvd_add_left (dvd_mul_right p _)).mp this
    obtain ⟨j, hj⟩ := hdiv
    have hc0 : 0 < c := by rcases Nat.eq_zero_or_pos c with h | h <;> [simp [h] at hqc; exact h]
    have hj0 : 0 < j := by rcases Nat.eq_zero_or_pos j with h | h <;> [simp [h] at hj; exact h]
    -- 1 + p + p^2 = (p c - 1)(p j - 1)
    rcases Nat.lt_or_ge c 2 with hc1 | hc2
    · have : c = 1 := by omega
      subst this; omega
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · have : j = 1 := by omega
      subst this
      -- k = p - 1, q*k = 1+p+p^2, q = p*c - 1
      have hk : k = p - 1 := by omega
      subst hk
      have e1 : (q:ℤ) * ((p:ℤ) - 1) = 1 + p + p^2 := by
        have := congrArg (Nat.cast : ℕ → ℤ) hk
        push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at this; linarith
      have e2 : (q:ℤ) = p * c - 1 := by
        have : ((q:ℤ) + 1) = p * c := by exact_mod_cast hqc
        linarith
      rw [e2] at e1
      have e3 : (c:ℤ) * ((p:ℤ) - 1) = p + 2 := by nlinarith
      have hc2' : (2:ℤ) ≤ c := by exact_mod_cast hc2
      have hp4 : p ≤ 4 := by
        have : (p:ℤ) ≤ 4 := by nlinarith
        exact_mod_cast this
      interval_cases p
      · have : c = 4 := by push_cast at e3; omega
        exact hpc (by rw [this]; norm_num)
      · push_cast at e3; omega
      · norm_num at hp
    · nlinarith
  · -- t = 2: q + 1 = p^2 * c, q < p^2
    simp at hqc
    have hc0 : c = 1 := by
      rcases c with _ | _ | c
      · simp at hqc
      · rfl
      · nlinarith
    subst hc0
    exfalso
    -- q = p^2 - 1 = (p-1)(p+1)
    have hfac : q = (p - 1) * (p + 1) := by
      have : p^2 = (p-1)*(p+1) + 1 := by
        rcases p with _ | p
        · omega
        · simp; ring
      omega
    have hd : p - 1 ∣ q := hfac ▸ dvd_mul_right _ _
    rcases (Nat.dvd_prime hq).mp hd with h | h
    · have hp2' : p = 2 := by omega
      subst hp2'
      exact hne ⟨rfl, by rw [hfac]⟩
    · omega
  · -- t ≥ 3: q ≥ p^3 contradiction with q < p^2
    exfalso
    have hc0 : 0 < c := by rcases Nat.eq_zero_or_pos c with h | h <;> [simp [h] at hqc; exact h]
    have h3 : p^2 * 2 ≤ p^(t+1+1+1) * c := by
      calc p^2 * 2 ≤ p^2 * p := Nat.mul_le_mul_left _ hp2
        _ = p^3 := by ring
        _ ≤ p^(t+1+1+1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ p^(t+1+1+1) * c := Nat.le_mul_of_pos_right _ hc0
    have : 4 ≤ p^2 := by nlinarith
    omega

theorem den_of (m n A : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : (∑ d ∈ m.divisors, d) * n = A * m) (hc : Nat.Coprime A n) :
    (((∑ d ∈ m.divisors, d : ℕ) : ℚ) / (m : ℚ)).den = n := by
  have e : (((∑ d ∈ m.divisors, d : ℕ) : ℚ) / (m : ℚ)) = ((A:ℤ):ℚ) / ((n:ℤ):ℚ) := by
    have hm' : (m:ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hn' : (n:ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have h' : ((∑ d ∈ m.divisors, d : ℕ) : ℚ) * n = A * m := by exact_mod_cast h
    push_cast
    rw [div_eq_div_iff hm' hn']
    push_cast at h'
    linarith
  rw [e]
  have := Rat.den_div_eq_of_coprime (a := (A:ℤ)) (b := (n:ℤ)) (by exact_mod_cast hn)
    (by simpa using hc)
  exact_mod_cast this

theorem sum_split (p k : ℕ) :
    ∑ i ∈ Finset.range (k+1), p^i = 1 + p * ∑ i ∈ Finset.range k, p^i := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

theorem not_dvd_S (p k : ℕ) (hp : p.Prime) : ¬ p ∣ ∑ i ∈ Finset.range (k+1), p^i := by
  rw [sum_split]
  intro h
  have : p ∣ 1 := (Nat.dvd_add_left (dvd_mul_right p _)).mp h
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem sigma_eq (m : ℕ) : ∑ d ∈ m.divisors, d = ArithmeticFunction.sigma 1 m := by
  rw [ArithmeticFunction.sigma_one_apply]

theorem pp_case (p a : ℕ) (hp : p.Prime) :
    ∃ m : ℕ, 0 < m ∧ (((∑ d ∈ m.divisors, d : ℕ) : ℚ) / (m : ℚ)).den = p ^ a := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  refine ⟨p ^ a, hpa, den_of _ _ (∑ d ∈ (p^a).divisors, d) hpa hpa (by ring) ?_⟩
  rw [sigma_eq, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  exact not_dvd_S p a hp

theorem semi_case (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ∃ m : ℕ, 0 < m ∧ (((∑ d ∈ m.divisors, d : ℕ) : ℚ) / (m : ℚ)).den = p * q := by
  by_cases h23 : p = 2 ∧ q = 3
  · obtain ⟨rfl, rfl⟩ := h23
    refine ⟨18, by norm_num, den_of 18 6 13 (by norm_num) (by norm_num) ?_ (by norm_num)⟩
    decide
  set t := (q+1).factorization p with ht
  set c := (q+1) / p ^ t with hc
  have hqc : q + 1 = p ^ t * c := (Nat.ordProj_mul_ordCompl_eq_self (q+1) p).symm
  have hpc : ¬ p ∣ c := Nat.not_dvd_ordCompl hp (by omega)
  have hcd : c ∣ q + 1 := Nat.ordCompl_dvd (q+1) p
  have hqc' : ¬ q ∣ c := by
    intro h
    have : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).mp (dvd_trans h hcd)
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hkey := key p q t c hp hq hpq h23 hqc hpc
  set S := ∑ i ∈ Finset.range (t+2), p^i with hS
  have hpS : ¬ p ∣ S := not_dvd_S p (t+1) hp
  have hcop : Nat.Coprime (p^(t+1)) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hq).mpr hpq.ne)
  have hsig : ∑ d ∈ (p^(t+1)*q).divisors, d = S * (q + 1) := by
    rw [sigma_eq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.sigma_one_apply_prime_pow hp]
    have : ArithmeticFunction.sigma 1 q = q + 1 := by
      have := ArithmeticFunction.sigma_one_apply_prime_pow hq (i := 1)
      simp [Finset.sum_range_succ] at this
      rw [this]; ring
    rw [this]
  have hm : 0 < p^(t+1)*q := Nat.mul_pos (pow_pos hp.pos _) hq.pos
  refine ⟨p^(t+1)*q, hm, den_of _ _ (S * c) hm (Nat.mul_pos hp.pos hq.pos) ?_ ?_⟩
  · rw [hsig, hqc]; ring
  · apply Nat.Coprime.mul_left
    · apply Nat.Coprime.mul_right
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]; exact hpS
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]; exact hkey
    · apply Nat.Coprime.mul_right
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]; exact hpc
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]; exact hqc'

def H1 : Prop := ∀ n : ℕ, 0 < n → 3 ≤ n.primeFactors.card →
  ∃ m : ℕ, 0 < m ∧ (((∑ d ∈ m.divisors, d : ℕ) : ℚ) / (m : ℚ)).den = n

def H2 : Prop := ∀ p q a b : ℕ, p.Prime → q.Prime → p ≠ q → 1 ≤ a → 1 ≤ b → 3 ≤ a + b →
  ∃ m : ℕ, 0 < m ∧ (((∑ d ∈ m.divisors, d : ℕ) : ℚ) / (m : ℚ)).den = p ^ a * q ^ b

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a162657.main := by
  intro h1 h2 n hn
  have hn0 : n ≠ 0 := hn.ne'
  rcases Nat.lt_or_ge n.primeFactors.card 3 with hk | hk
  swap
  · exact h1 n hn hk
  interval_cases hcard : n.primeFactors.card
  · have : n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hcard) with h | h
      · omega
      · exact h
    subst this
    exact ⟨1, by norm_num, by simp⟩
  · obtain ⟨p, hp1⟩ := Finset.card_eq_one.mp hcard
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (hp1 ▸ Finset.mem_singleton_self p)
    have : n = p ^ n.primeFactorsList.length := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd hn0
      intro d hd hdn
      have : d ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdn, hn0⟩
      rw [hp1] at this; simpa using this
    rw [this]; exact pp_case p _ hp
  · obtain ⟨p, q, hpq, hpq1⟩ := Finset.card_eq_two.mp hcard
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hpq1]; simp)
    have hq : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hpq1]; simp)
    have hprod : n = p ^ n.factorization p * q ^ n.factorization q := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization, hpq1, Finset.prod_pair hpq]
    have ha : 1 ≤ n.factorization p := by
      have : p ∈ n.primeFactors := by rw [hpq1]; simp
      rw [← Nat.support_factorization, Finsupp.mem_support_iff] at this; omega
    have hb : 1 ≤ n.factorization q := by
      have : q ∈ n.primeFactors := by rw [hpq1]; simp
      rw [← Nat.support_factorization, Finsupp.mem_support_iff] at this; omega
    rcases Nat.lt_or_ge (n.factorization p + n.factorization q) 3 with hs | hs
    · have ea : n.factorization p = 1 := by omega
      have eb : n.factorization q = 1 := by omega
      rw [ea, eb, pow_one, pow_one] at hprod
      rw [hprod]
      rcases Nat.lt_or_gt_of_ne hpq with hlt | hgt
      · exact semi_case p q hp hq hlt
      · rw [mul_comm]; exact semi_case q p hq hp hgt
    · rw [hprod]; exact h2 p q _ _ hp hq hpq ha hb hs

end OMA.R_oeis_a162657_R1
