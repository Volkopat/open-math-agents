import OMAStatements.S_oeis_a247938

-- Problem: A247938: Sum of divisors of 2^prime(n)-1.
-- Credit: @sobrien032

/-!
Jianing Song conjectured the exact maximum in 2022 for OEIS A247938,
a sequence contributed by Vincenzo Librandi. The result of Bojanić on the
limiting ratio, cited in the entry, concerns the asymptotic question.

For prime exponents p at least 23, the order of 2 modulo each prime
divisor q of the Mersenne number forces q to be 1 modulo 2p. At most
two such q are less than 6p, and the product of all distinct prime
factors bounds their number. The resulting sum of reciprocals controls
the divisor sum by the finite geometric product formula. Checking the
smaller prime exponents gives equality at the fifth prime, 11.

Elementary argument and Lean formalization by Codex.
-/

namespace Mersenne

theorem factor_congruence {p q : ℕ} (hp : p.Prime) (hp23 : 23 ≤ p)
    (hq : q ∈ (2^p-1).primeFactors) : 2*p ∣ q-1 := by
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hd := Nat.dvd_of_mem_primeFactors hq
  let : Fact q.Prime := ⟨hprime⟩
  let : Fact p.Prime := ⟨hp⟩
  have hpow : (2 : ZMod q)^p = 1 := by
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, sub_eq_zero] at hz
    exact hz
  have hn : (2 : ZMod q) ≠ 0 := by
    intro hz
    rw [hz, zero_pow hp.ne_zero] at hpow
    exact zero_ne_one hpow
  have hone : (2 : ZMod q) ≠ 1 := by
    intro h
    have hh : (1 : ZMod q) = 0 := by linear_combination h
    exact one_ne_zero hh
  have hord := orderOf_eq_prime hpow hone
  have hpdiv : p ∣ q-1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hn
  have hq2 : q ≠ 2 := by
    intro he
    have hd2 : q ∣ 2 := he ▸ dvd_refl _
    exact hn (by exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).2 hd2)
  exact Nat.Prime.dvd_mul_of_dvd_ne (by omega) Nat.prime_two hp
    (even_iff_two_dvd.mp (hprime.even_sub_one hq2)) hpdiv

end Mersenne

namespace Mersenne

theorem reciprocal_bound {p : ℕ} (hp : 23 ≤ p)
    (hdiv : ∀ q ∈ (2^p-1).primeFactors, 2*p ∣ q-1) :
    ((2^p-1).primeFactors.sum (fun q : ℕ ↦ (1:ℚ)/q)) ≤ 7/135 := by
  classical
  let F := (2^p-1).primeFactors
  have hpos : 1 < 2^p := one_lt_pow₀ (by decide) (by omega)
  have hq (q : ℕ) (h : q ∈ F) : 2*p < q := by
    have hprime := Nat.prime_of_mem_primeFactors h
    have hmin := Nat.le_of_dvd (by have := hprime.two_le; omega) (hdiv q h)
    omega
  have hcount : 5*F.card < p := by
    have hbound : 2^(5*F.card) ≤ 2^p-1 := calc
      _ = ∏ _q ∈ F, (32:ℕ) := by simp [pow_mul]
      _ ≤ ∏ q ∈ F, q := Finset.prod_le_prod' fun q h ↦ by have := hq q h; omega
      _ ≤ 2^p-1 := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 (by omega)
  have hterm (q : ℕ) (h : q ∈ F) :
      (12*(p:ℚ))* (1/(q:ℚ)) ≤ 2 + (if q=2*p+1 then 4 else 0) +
        (if q=4*p+1 then 1 else 0) := by
    have hlarge := hq q h
    have hqp : (0:ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ hqp).mpr
    by_cases h1 : q=2*p+1
    · have h2 : q ≠ 4*p+1 := by omega
      rw [if_pos h1, if_neg h2, h1]
      push_cast
      linarith
    by_cases h2 : q=4*p+1
    · rw [if_neg h1, if_pos h2, h2]
      push_cast
      linarith
    obtain ⟨k,hk⟩ := hdiv q h
    have hk3 : 3 ≤ k := by
      by_contra! hh
      interval_cases k <;> omega
    have h3 := Nat.mul_le_mul_left (2*p) hk3
    have hlarge3 : 6*p ≤ q := by omega
    have hcast : 6*(p:ℚ) ≤ q := by exact_mod_cast hlarge3
    simp [h1,h2]
    linarith
  have hsingle (a : ℕ) (w : ℚ) (hw : 0 ≤ w) :
      (∑ q ∈ F, if q=a then w else 0) ≤ w := by
    rw [Finset.sum_ite_eq' F a (fun _ ↦ w)]
    split <;> simp_all
  have hS : (12*(p:ℚ))*(∑ q ∈ F, (1:ℚ)/q) ≤ 2*(F.card:ℚ)+5 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    linarith [hsingle (2*p+1) 4 (by norm_num), hsingle (4*p+1) 1 (by norm_num)]
  have hcardQ : 5*(F.card:ℚ) < p := by exact_mod_cast hcount
  have hpQ : (23:ℚ) ≤ p := by exact_mod_cast hp
  have hfin : 2*(F.card:ℚ)+5 ≤ 12*(p:ℚ)*(7/135) := by linarith
  change (∑ q ∈ F, (1:ℚ)/q) ≤ 7/135
  exact le_of_mul_le_mul_left (a := 12*(p:ℚ)) (hS.trans hfin) (by positivity)

end Mersenne

namespace Mersenne

private theorem reciprocal_product_lower (s : Finset ℕ) (hs : ∀ q ∈ s, 2 ≤ q) :
    1 - ∑ q ∈ s, (1 : ℚ)/q ≤ ∏ q ∈ s, (1 - (1 : ℚ)/q) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hqs ih =>
    have hq : 2 ≤ q := hs q (Finset.mem_insert_self _ _)
    have done := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
    have hq' : (1:ℚ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hq0 : (0:ℚ) < q := by linarith
    have nonneg : 0 ≤ 1-(1:ℚ)/q := by
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hq0).mpr
      simpa using hq'
    have hsum : 0 ≤ ∑ r ∈ s, (1:ℚ)/r := Finset.sum_nonneg (fun _ _ => by positivity)
    rw [Finset.sum_insert hqs, Finset.prod_insert hqs]
    calc
      1 - (1/(q:ℚ) + ∑ r ∈ s, (1:ℚ)/r) ≤
          (1-1/(q:ℚ))*(1-∑ r ∈ s, (1:ℚ)/r) := by
            nlinarith [mul_nonneg (show 0 ≤ (1:ℚ)/q by positivity) hsum]
      _ ≤ _ := mul_le_mul_of_nonneg_left done nonneg

private theorem geometric_factor_bound (q : ℚ) (hq : 0 < q) (e : ℕ) :
    (∑ i ∈ Finset.range (e+1), q^i) * (1-1/q) ≤ q^e := by
  rw [show 1 - 1/q = (q-1)/q by field_simp, ← mul_div_assoc, geom_sum_mul, pow_succ]
  apply (div_le_iff₀ hq).mpr
  linarith

theorem sigma_bound {n : ℕ} (hn : n ≠ 0) :
    (ArithmeticFunction.sigma 1 n : ℚ) * (1 - ∑ q ∈ n.primeFactors, (1:ℚ)/q) ≤ n := by
  have hsigma : (ArithmeticFunction.sigma 1 n : ℚ) =
      ∏ q ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization q + 1), (q:ℚ)^i := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
    push_cast
    simp
  have hnprod : (n : ℚ) = ∏ q ∈ n.primeFactors, (q : ℚ)^(n.factorization q) := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  calc
    _ ≤ (ArithmeticFunction.sigma 1 n : ℚ) * ∏ q ∈ n.primeFactors, (1-(1:ℚ)/q) :=
      mul_le_mul_of_nonneg_left
        (reciprocal_product_lower _ fun _ hq => (Nat.prime_of_mem_primeFactors hq).two_le)
        (by positivity)
    _ = ∏ q ∈ n.primeFactors,
          (∑ i ∈ Finset.range (n.factorization q+1), (q:ℚ)^i) * (1-1/(q:ℚ)) := by
      rw [hsigma, Finset.prod_mul_distrib]
    _ ≤ ∏ q ∈ n.primeFactors, (q : ℚ)^(n.factorization q) := by
      apply Finset.prod_le_prod
      · intro q hq
        have hq1 : (1:ℚ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le
        have hq0 : (0:ℚ) < q := by linarith
        exact mul_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
          (sub_nonneg.mpr ((div_le_iff₀ hq0).mpr (by simpa using hq1)))
      · intro q hq
        apply geometric_factor_bound
        exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
    _ = n := hnprod.symm

end Mersenne

namespace Mersenne

open ArithmeticFunction OMA.S_oeis_a247938

private theorem sigma_prime_value {q : ℕ} (hq : q.Prime) : sigma 1 q = q+1 := by
  simpa [Finset.sum_range_succ, add_comm] using sigma_one_apply_prime_pow (i := 1) hq

private theorem eleven_value :
    (sigma 1 (2^11-1) : ℚ) / 2^11 = 135/128 := by
  change (sigma 1 (23*89) : ℚ) / 2^11 = 135/128
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime 23 89),
    sigma_prime_value (by decide : Nat.Prime 23), sigma_prime_value (by decide : Nat.Prime 89)]
  norm_num

theorem small_bound {p : ℕ} (hp : p.Prime) (hlt : p < 23) :
    (sigma 1 (2^p-1) : ℚ) / 2^p ≤ 135/128 := by
  have cases_p : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 := by
    interval_cases p <;> norm_num at *
  by_cases h11 : p = 11
  · subst p
    exact eleven_value.le
  have hm : (2^p-1).Prime := by
    rcases cases_p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at *
  have hp2 : 1 ≤ 2^p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [sigma_prime_value hm, Nat.sub_add_cancel hp2]
  norm_num

theorem fifth_ratio : ratio 5 = 135/128 := by
  have h : prime 5 = 11 := Nat.nth_prime_four_eq_eleven
  simpa only [ratio, h] using eleven_value

end Mersenne

namespace Mersenne

private theorem prime_ratio_bound {p : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.sigma 1 (2^p-1) : ℚ) / 2^p ≤ 135/128 := by
  by_cases h : p < 23
  · exact small_bound hp h
  have hp23 := Nat.le_of_not_gt h
  have hr := reciprocal_bound hp23 (fun _ hq ↦ factor_congruence hp hp23 hq)
  have hpow : 1 < (2:ℕ)^p := one_lt_pow₀ (by decide) hp.ne_zero
  have hn : 2^p-1 ≠ 0 := by omega
  have hs := sigma_bound hn
  have hle : (ArithmeticFunction.sigma 1 (2^p-1) : ℚ) * (128/135) ≤ (2^p-1 : ℕ) := by
    apply le_trans _ hs
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith
  apply (div_le_iff₀ (by positivity)).2
  rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hle
  linarith

end Mersenne

open OMA.S_oeis_a247938 in
theorem OMA.solution : type_of% @OMA.S_oeis_a247938.main := by
  refine ⟨⟨⟨5, by decide, Mersenne.fifth_ratio.symm⟩, ?_⟩, Mersenne.fifth_ratio⟩
  rintro x ⟨n, _, rfl⟩
  exact Mersenne.prime_ratio_bound (Nat.prime_nth_prime (n-1))
