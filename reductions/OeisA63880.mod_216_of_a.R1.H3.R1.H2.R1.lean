import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1

-- Reduction OeisA63880.mod_216_of_a.R1.H3.R1.H2.R1 of step OeisA63880.mod_216_of_a.R1.H3.R1.H2
-- Credit: @Ciphore
-- In the exponent-one case `m = 3 * t` the factor `3` contributes equally to both
-- divisor sums, so the equation descends unchanged to the coprime-to-`3` cofactor.
-- Squarefree and prime-power cofactors are excluded outright, and the remaining
-- core is split by the number of distinct prime factors.

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H2_R1

open OeisA63880
open scoped ArithmeticFunction.sigma

private theorem splitUnitary {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) :
    unitaryDivisors (m*q) = unitaryDivisors m ∪ (unitaryDivisors m).image (· * q) := by
  have hq0 := hq.pos
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨t, ht⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_mul_pos_right (ht ▸ Nat.mul_pos hm hq0)
    rw [ht, Nat.mul_div_cancel_left _ hd0] at hcd
    have hqt : q ∣ d*t := ht ▸ dvd_mul_left q m
    rcases (hcd.isPrimePow_dvd_mul hq).1 hqt with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have he : m = b*t := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      have hb : 0 < b := Nat.pos_of_mul_pos_left hd0
      exact Or.inr ⟨b, ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hb] using (Nat.coprime_mul_iff_left.1 hcd).2⟩, mul_comm ..⟩
    · have he : m = d*b := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      exact Or.inl ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hd0] using (Nat.coprime_mul_iff_right.1 hcd).2⟩
  · rintro (⟨⟨⟨t, rfl⟩, -⟩, hcd⟩ | ⟨b, ⟨⟨⟨t, rfl⟩, -⟩, hcd⟩, rfl⟩)
    · have hd := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) q, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd]
      exact hcd.mul_right (Nat.coprime_mul_iff_right.1 hc).1.symm
    · have hb := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hb] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right b t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_right_comm b t q, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hq0)]
      exact hcd.mul_left (Nat.coprime_mul_iff_right.1 hc).2

private theorem unitarySum {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) : usigma (m*q) = usigma m * (q+1) := by
  have dis : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * q)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hd'
    have dvd : b*q ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
    exact hq.ne_one (hc.eq_one_of_dvd ((dvd_mul_left q b).trans dvd))
  unfold usigma
  rw [splitUnitary hm hq hc, Finset.sum_union dis,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq.pos h),
    ← Finset.sum_mul, mul_add, mul_one, add_comm]

theorem usigma_le_sigma (t : ℕ) : usigma t ≤ σ 1 t := by
  unfold usigma
  rw [ArithmeticFunction.sigma_one_apply]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact (Finset.mem_filter.1 hx).1
  · intro x _ _
    exact Nat.zero_le x

theorem usigma_pos {t : ℕ} (ht : 0 < t) : 0 < usigma t := by
  unfold usigma
  have h1 : 1 ∈ unitaryDivisors t := by
    rw [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd t, ht.ne'⟩, Nat.coprime_one_left _⟩
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) h1

/-- Exact prime-power extraction: if `p^2 ∣ t`, write `t = p^a * u` with
`a = t.factorization p`, `2 ≤ a`, and `¬ p ∣ u`. -/
theorem exact_power_extraction {t p : ℕ} (ht : 0 < t) (hp : p.Prime) (hdiv : p ^ 2 ∣ t) :
    ∃ a u : ℕ, t = p ^ a * u ∧ 2 ≤ a ∧ ¬ p ∣ u ∧ 0 < u := by
  have ht0 : t ≠ 0 := ht.ne'
  have a_def : t.factorization p ≥ 2 := (hp.pow_dvd_iff_le_factorization ht0).1 hdiv
  set a := t.factorization p with ha
  have hpa : p ^ a ∣ t := (hp.pow_dvd_iff_le_factorization ht0).2 (le_refl a)
  refine ⟨a, t / p ^ a, (Nat.mul_div_cancel' hpa).symm, a_def, ?_, ?_⟩
  · intro hpu
    obtain ⟨s, hs⟩ := hpu
    have hpp1 : p ^ (a + 1) ∣ t := by
      use s
      have hm : t = p ^ a * (t / p ^ a) := (Nat.mul_div_cancel' hpa).symm
      rw [hm, hs]
      ring
    have hle := (hp.pow_dvd_iff_le_factorization ht0).1 hpp1
    omega
  · rcases Nat.eq_zero_or_pos (t / p ^ a) with hz | hp2
    · have hm : t = p ^ a * (t / p ^ a) := (Nat.mul_div_cancel' hpa).symm
      rw [hz, mul_zero] at hm
      exact absurd hm ht0
    · exact hp2

/-- For squarefree `t`, every divisor is unitary. -/
theorem sqfree_unitaryDivisors {t : ℕ} (hsq : Squarefree t) :
    unitaryDivisors t = t.divisors := by
  ext d
  simp only [unitaryDivisors, Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro hd
    refine ⟨hd, ?_⟩
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, htpos⟩ := hd
    -- show coprime d (t/d): any common prime factor would square-divide t
    by_contra hnc
    have htpos' : t ≠ 0 := htpos
    have hd0 : d ≠ 0 := by
      intro hz
      rw [hz] at hdvd
      exact htpos' (Nat.eq_zero_of_zero_dvd hdvd)
    have hg1 : Nat.gcd d (t / d) ≠ 1 := hnc
    have hgpos : 0 < Nat.gcd d (t / d) := Nat.gcd_pos_of_pos_left (t / d) (Nat.pos_of_ne_zero hd0)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg1
    have hd1 : p ∣ d := hpdvd.trans (Nat.gcd_dvd_left d (t / d))
    have hd2 : p ∣ t / d := hpdvd.trans (Nat.gcd_dvd_right d (t / d))
    have hsq2 : p * p ∣ t := by
      obtain ⟨a, ha⟩ := hd1
      obtain ⟨b, hb⟩ := hd2
      have htd : t = d * (t / d) := (Nat.mul_div_cancel' hdvd).symm
      rw [htd, hb, ha]
      use a * b
      ring
    have := hsq p hsq2
    exact hp.ne_one (Nat.isUnit_iff.1 this)

/-- For squarefree `t`, the unitary and ordinary divisor sums agree. -/
theorem usigma_eq_sigma_of_squarefree {t : ℕ} (hsq : Squarefree t) :
    usigma t = σ 1 t := by
  unfold usigma
  rw [sqfree_unitaryDivisors hsq, ArithmeticFunction.sigma_one_apply]


theorem usigma_one : usigma 1 = 1 := by
  decide

theorem usigma_primepow {q : ℕ} (hq : IsPrimePow q) : usigma q = q + 1 := by
  have h := unitarySum (m := 1) (q := q) one_pos hq (Nat.coprime_one_right q)
  rwa [one_mul, usigma_one, one_mul] at h

theorem sigma_three : σ 1 3 = 4 := by
  have h : (3 : ℕ) = 3 ^ 1 := by norm_num
  rw [h, ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three]
  norm_num [Finset.sum_range_succ]

theorem usigma_three : usigma 3 = 4 :=
  usigma_primepow ((isPrimePow_nat_iff _).2 ⟨3, 1, Nat.prime_three, by norm_num, by norm_num⟩)

/-- The exponent-one case descends to the coprime cofactor with the same equation. -/
theorem transformed_one {m : ℕ} (hm : m ≠ 0) (hf : m.factorization 3 = 1)
    (hr : 7 * σ 1 m = 10 * usigma m) :
    7 * σ 1 (m / 3) = 10 * usigma (m / 3) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hdvd : 3 ∣ m := by
    have h32 : 3 ^ 1 ∣ m := (hp.pow_dvd_iff_le_factorization hm).2 (by omega)
    simpa using h32
  have hndvd : ¬ 3 ∣ (m / 3) := by
    intro h3t
    obtain ⟨s, hs⟩ := h3t
    have hm3 : m = 3 * (m / 3) := (Nat.mul_div_cancel' hdvd).symm
    have h9 : 3 ^ 2 ∣ m := by
      use s
      rw [hm3, hs]
      ring
    have hle := (hp.pow_dvd_iff_le_factorization hm).1 h9
    omega
  set t := m / 3 with ht
  have hm3 : m = 3 * t := (Nat.mul_div_cancel' hdvd).symm
  have hcop3 : Nat.Coprime 3 t := (Nat.prime_three.coprime_iff_not_dvd).2 hndvd
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with hz | hp2
    · rw [hz, mul_zero] at hm3
      exact absurd hm3 hm
    · exact hp2
  have h3pp : IsPrimePow (3 : ℕ) :=
    (isPrimePow_nat_iff _).2 ⟨3, 1, Nat.prime_three, by norm_num, by norm_num⟩
  have hsg : σ 1 m = 4 * σ 1 t := by
    rw [hm3, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop3, sigma_three]
  have hug : usigma m = 4 * usigma t := by
    have hcomm : m = t * 3 := by rw [hm3, mul_comm]
    rw [hcomm, unitarySum htpos h3pp hcop3]
    ring
  rw [hsg, hug] at hr
  omega

/-- In the descended equation the cofactor cannot be a prime power:
reduction modulo the prime forces `p ∣ 3`. -/
theorem not_primepow_of_equation10 {t : ℕ} (ht3 : ¬ 3 ∣ t)
    (hr : 7 * σ 1 t = 10 * usigma t) : ¬ IsPrimePow t := by
  intro hpw
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff t).1 hpw
  rw [usigma_primepow ((isPrimePow_nat_iff _).2 ⟨p, e, hp, he, rfl⟩),
    ArithmeticFunction.sigma_one_apply_prime_pow hp] at hr
  have hsplit : ∑ i ∈ Finset.range (e + 1), p ^ i = 1 + p * ∑ i ∈ Finset.range e, p ^ i := by
    rw [Finset.sum_range_succ']
    rw [Finset.mul_sum]
    rw [show (∑ x ∈ Finset.range e, p ^ (x + 1)) = ∑ x ∈ Finset.range e, p * p ^ x from
      Finset.sum_congr rfl fun i _ => pow_succ' p i]
    rw [pow_zero, add_comm]
  rw [hsplit] at hr
  obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [pow_succ] at hr
  set S := ∑ i ∈ Finset.range (e' + 1), p ^ i with hS
  have key : 7 * p * S = 10 * (p ^ e' * p) + 3 := by
    have h7 : 7 * (1 + p * S) = 7 + 7 * p * S := by ring
    have h10 : 10 * (p ^ e' * p + 1) = 10 * (p ^ e' * p) + 10 := by ring
    rw [h7, h10] at hr
    omega
  have hdvd3 : p ∣ 3 := by
    have keyZ : (7 : ℤ) * p * S = 10 * (p ^ e' * p) + 3 := by exact_mod_cast key
    have hd1Z : (p : ℤ) ∣ 7 * p * S := ⟨7 * S, by ring⟩
    have hd2Z : (p : ℤ) ∣ 10 * (p ^ e' * p) := ⟨10 * p ^ e', by ring⟩
    have hsub : (p : ℤ) ∣ (7 * p * S - 10 * (p ^ e' * p)) := dvd_sub hd1Z hd2Z
    have heq : (7 : ℤ) * p * S - 10 * (p ^ e' * p) = 3 := by omega
    rw [heq] at hsub
    exact_mod_cast hsub
  have hp3 : p = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd p hdvd3 with h1 | h3eq
    · exact absurd h1 hp.ne_one
    · exact h3eq
  subst hp3
  exact ht3 (dvd_pow_self 3 (by omega))

/-- The residual core whose exponents are all even: perfect-square cofactors. -/
def H1 : Prop := ∀ t : ℕ, Odd t → ¬ 3 ∣ t → ¬ Squarefree t → ¬ IsPrimePow t →
  IsSquare t → 7 * σ 1 t ≠ 10 * usigma t

/-- The residual core with at least one odd exponent: non-square cofactors. -/
def H2 : Prop := ∀ t : ℕ, Odd t → ¬ 3 ∣ t → ¬ Squarefree t → ¬ IsPrimePow t →
  ¬ IsSquare t → 7 * σ 1 t ≠ 10 * usigma t

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1.H2 := by
  intro h1 h2 m ho hr hf1
  have hm : m ≠ 0 := by
    obtain ⟨k, hk⟩ := ho
    omega
  have hdvd : 3 ∣ m := by
    have h32 : 3 ^ 1 ∣ m := (Nat.prime_three.pow_dvd_iff_le_factorization hm).2 (by omega)
    simpa using h32
  set t := m / 3 with ht
  have hm3 : m = 3 * t := (Nat.mul_div_cancel' hdvd).symm
  have ht_eq := transformed_one hm hf1 hr
  have hndvd : ¬ 3 ∣ t := by
    intro h3t
    obtain ⟨s, hs⟩ := h3t
    have h9 : 3 ^ 2 ∣ m := by
      use s
      rw [hm3, hs]
      ring
    have hle := (Nat.prime_three.pow_dvd_iff_le_factorization hm).1 h9
    omega
  have htodd : Odd t := by
    obtain ⟨k, hk⟩ := ho
    use (k - 1 * t)
    omega
  -- squarefree cofactor impossible: divisor sums agree, forcing `7 = 10`
  by_cases hsq : Squarefree t
  · have huv := usigma_eq_sigma_of_squarefree hsq
    rw [huv] at ht_eq
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with hz | hp2
      · rw [hz, mul_zero] at hm3
        exact absurd hm3 hm
      · exact hp2
    have hspos : 0 < σ 1 t := by
      obtain ⟨k, hk⟩ := htodd
      have ht0 : t ≠ 0 := by omega
      rw [ArithmeticFunction.sigma_one_apply]
      have hmem : t ∈ t.divisors := Nat.mem_divisors.2 ⟨dvd_rfl, ht0⟩
      have hle : t ≤ ∑ d ∈ t.divisors, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hmem
      omega
    have heq7 : 7 = 10 := Nat.eq_of_mul_eq_mul_right hspos ht_eq
    norm_num at heq7
  · have hnp : ¬ IsPrimePow t := not_primepow_of_equation10 hndvd ht_eq
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with hz | hp2
      · rw [hz, mul_zero] at hm3
        exact absurd hm3 hm
      · exact hp2
    by_cases hsqt : IsSquare t
    · exact h1 t htodd hndvd hsq hnp hsqt ht_eq
    · exact h2 t htodd hndvd hsq hnp hsqt ht_eq

end OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H2_R1
