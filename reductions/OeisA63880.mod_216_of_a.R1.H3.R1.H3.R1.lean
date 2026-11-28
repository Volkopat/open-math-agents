import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1
import Mathlib.Tactic

-- Reduction OeisA63880.mod_216_of_a.R1.H3.R1.H3.R1 of step OeisA63880.mod_216_of_a.R1.H3.R1.H3
-- Credit: @Ciphore
-- In the exponent-two case the equation transforms into `91 * σ 1 t = 100 * usigma t`
-- on the cofactor `t = m / 9`; prime-power cofactors are excluded by a modular argument,
-- and the remaining sieve core splits by squarefreeness.

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1

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

theorem usigma_one : usigma 1 = 1 := by
  decide

theorem usigma_primepow {q : ℕ} (hq : IsPrimePow q) : usigma q = q + 1 := by
  have h := unitarySum (m := 1) (q := q) one_pos hq (Nat.coprime_one_right q)
  rwa [one_mul, usigma_one, one_mul] at h

theorem sigma_nine : σ 1 9 = 13 := by
  have h : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h, ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three]
  norm_num [Finset.sum_range_succ]

theorem usigma_nine : usigma 9 = 10 := by
  have hpp : IsPrimePow (9 : ℕ) :=
    (isPrimePow_nat_iff _).2 ⟨3, 2, Nat.prime_three, by norm_num, by norm_num⟩
  rw [usigma_primepow hpp]

/-- Divisibility consequences of the exponent-two factorization. -/
theorem cofactor_spec {m : ℕ} (hm : m ≠ 0) (hf : m.factorization 3 = 2) :
    9 ∣ m ∧ ¬ 3 ∣ (m / 9) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hdvd : 3 ^ 2 ∣ m := (hp.pow_dvd_iff_le_factorization hm).2 (by omega)
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  have hdvd9 : 9 ∣ m := by
    rw [h9]
    exact hdvd
  refine ⟨hdvd9, fun h3t => ?_⟩
  obtain ⟨s, hs⟩ := h3t
  have hm9 : m = 9 * (m / 9) := (Nat.mul_div_cancel' hdvd9).symm
  have h27 : 3 ^ 3 ∣ m := by
    use s
    rw [hm9, hs]
    ring
  have hle := (hp.pow_dvd_iff_le_factorization hm).1 h27
  omega

/-- The equation transformation in the exponent-two case. -/
theorem transformed {m : ℕ} (hm : m ≠ 0) (hf : m.factorization 3 = 2)
    (hr : 7 * σ 1 m = 10 * usigma m) :
    91 * σ 1 (m / 9) = 100 * usigma (m / 9) := by
  obtain ⟨hdvd, hndvd⟩ := cofactor_spec hm hf
  set t := m / 9 with ht
  have hm9 : m = 9 * t := (Nat.mul_div_cancel' hdvd).symm
  have hcop3 : Nat.Coprime 3 t := (Nat.prime_three.coprime_iff_not_dvd).2 hndvd
  have hcop9 : Nat.Coprime 9 t := by
    have h33 : Nat.Coprime (3 * 3) t := Nat.coprime_mul_iff_left.2 ⟨hcop3, hcop3⟩
    norm_num at h33
    exact h33
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with hz | hp
    · rw [hz, mul_zero] at hm9
      exact absurd hm9 hm
    · exact hp
  have h9pp : IsPrimePow (9 : ℕ) :=
    (isPrimePow_nat_iff _).2 ⟨3, 2, Nat.prime_three, by norm_num, by norm_num⟩
  have hsg : σ 1 m = 13 * σ 1 t := by
    rw [hm9, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop9, sigma_nine]
  have hug : usigma m = 10 * usigma t := by
    have hcomm : m = t * 9 := by rw [hm9, mul_comm]
    rw [hcomm, unitarySum htpos h9pp hcop9]
    ring
  rw [hsg, hug] at hr
  omega

/-- In the transformed equation, `t` cannot be a prime power. -/
theorem not_primepow_of_equation {t : ℕ} (ht3 : ¬ 3 ∣ t)
    (hr : 91 * σ 1 t = 100 * usigma t) : ¬ IsPrimePow t := by
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
  -- expanded equation: `91 + 91 * p * S = 100 * p ^ e + 100`
  have hepos : 0 < e := he
  obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [pow_succ] at hr
  set S := ∑ i ∈ Finset.range (e' + 1), p ^ i with hS
  have key : 91 * p * S = 100 * (p ^ e' * p) + 9 := by
    have h91 : 91 * (1 + p * S) = 91 + 91 * p * S := by ring
    have h100 : 100 * (p ^ e' * p + 1) = 100 * (p ^ e' * p) + 100 := by ring
    rw [h91, h100] at hr
    omega
  have hdvd9 : p ∣ 9 := by
    have keyZ : (91 : ℤ) * p * S = 100 * (p ^ e' * p) + 9 := by exact_mod_cast key
    have hd1Z : (p : ℤ) ∣ 91 * p * S := ⟨91 * S, by ring⟩
    have hd2Z : (p : ℤ) ∣ 100 * (p ^ e' * p) := ⟨100 * p ^ e', by ring⟩
    have hsub : (p : ℤ) ∣ (91 * p * S - 100 * (p ^ e' * p)) := dvd_sub hd1Z hd2Z
    have heq : (91 : ℤ) * p * S - 100 * (p ^ e' * p) = 9 := by omega
    rw [heq] at hsub
    exact_mod_cast hsub
  have hp3 : p = 3 := by
    have h32 : (9 : ℕ) = 3 ^ 2 := by norm_num
    have hd93 : p ∣ 3 ^ 2 := by
      rw [← h32]
      exact hdvd9
    have h3 : p ∣ 3 := Nat.Prime.dvd_of_dvd_pow hp hd93
    rcases Nat.prime_three.eq_one_or_self_of_dvd p h3 with h1 | h3eq
    · exact absurd h1 hp.ne_one
    · exact h3eq
  subst hp3
  exact ht3 (dvd_pow_self 3 (by omega))

/-- The residual sieve core: squarefree cofactors. -/
def H1 : Prop := ∀ t : ℕ, Odd t → ¬ 3 ∣ t → Squarefree t → ¬ IsPrimePow t →
  91 * σ 1 t ≠ 100 * usigma t

/-- The residual sieve core: non-squarefree cofactors. -/
def H2 : Prop := ∀ t : ℕ, Odd t → ¬ 3 ∣ t → ¬ Squarefree t → ¬ IsPrimePow t →
  91 * σ 1 t ≠ 100 * usigma t

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1.H3 := by
  intro h1 h2 m ho hr hf2
  have hm : m ≠ 0 := by
    obtain ⟨k, hk⟩ := ho
    omega
  obtain ⟨hdvd, hndvd⟩ := cofactor_spec hm hf2
  set t := m / 9 with ht
  have ht_eq := transformed hm hf2 hr
  have htodd : Odd t := by
    obtain ⟨k, hk⟩ := ho
    have hm9 : m = 9 * t := (Nat.mul_div_cancel' hdvd).symm
    use (k - 4 * t)
    omega
  have hnp : ¬ IsPrimePow t := not_primepow_of_equation hndvd ht_eq
  by_cases hsq : Squarefree t
  · exact h1 t htodd hndvd hsq hnp ht_eq
  · exact h2 t htodd hndvd hsq hnp ht_eq

end OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1
