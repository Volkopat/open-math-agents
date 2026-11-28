import FormalConjectures.Wikipedia.HyperperfectNumber

/-! # A reduction of the infinitude of hyperperfect numbers

An unbounded supply of prime parameters from two classical constructions
would yield infinitely many hyperperfect numbers with index at least two.
-/

-- Credit: @MistyDay86
-- Two prime families from J. S. McCranie, A Study of Hyperperfect Numbers
-- (2000), Theorems 1 and 3: https://cs.uwaterloo.ca/journals/JIS/VOL3/mccranie.html

namespace OMA.R_HyperperfectNumber_infinitely_many_hyperperfect_numbers_R1

open HyperperfectNumber ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem sigma_prime_power_mul_prime {p q e : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    σ 1 (p ^ e * q) = (∑ i ∈ Finset.range (e + 1), p ^ i) * (q + 1) := by
  have hc : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  have hq' : σ 1 q = q + 1 := by
    simpa using (sigma_one_apply_prime_pow (i := 1) hq)
  rw [isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left e),
    sigma_one_apply_prime_pow hp, hq']

private theorem hyperperfect_of_sigma {k n : ℕ}
    (hk : 0 < k) (hn : 1 < n)
    (h : k * σ 1 n + 1 = (k + 1) * n + k) : IsHyperperfect k n := by
  have hs : 1 ≤ ∑ d ∈ n.properDivisors, d :=
    Finset.single_le_sum (fun d _ ↦ Nat.zero_le d)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr hn)
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    Nat.mul_add, Nat.add_mul, one_mul] at h
  exact ⟨hk, hn, by rw [Nat.mul_sub_left_distrib, mul_one]; omega⟩

/-- The linear prime pair gives the odd-index family. -/
theorem linear_pair {t : ℕ} (hp : (6 * t + 5).Prime) (hq : (12 * t + 13).Prime) :
    IsHyperperfect (4 * t + 3) ((6 * t + 5) ^ 2 * (12 * t + 13)) := by
  apply hyperperfect_of_sigma (by omega)
  · have h : 6 * t + 5 ≤ (6 * t + 5) ^ 2 * (12 * t + 13) := by
      calc
        6 * t + 5 ≤ (6 * t + 5) ^ 2 := by nlinarith
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · rw [sigma_prime_power_mul_prime hp hq (by omega)]
    norm_num [Finset.sum_range_succ]
    ring

/-- The prime shift of a prime power gives the family with index `p - 1`. -/
theorem power_shift {p e : ℕ} (hp3 : 3 ≤ p) (he : 1 ≤ e)
    (hp : p.Prime) (hq : (p ^ (e + 1) - (p - 1)).Prime) :
    IsHyperperfect (p - 1) (p ^ e * (p ^ (e + 1) - (p - 1))) := by
  let q := p ^ (e + 1) - (p - 1)
  let k := p - 1
  have hp' : k + 1 = p := by dsimp [k]; omega
  have hpe : p ≤ p ^ e := by
    simpa using (pow_right_monotone (a := p) (by omega : 1 ≤ p) he)
  have hq_add : q + k = p ^ (e + 1) := by
    dsimp only [q, k]
    apply Nat.sub_add_cancel
    have : p ≤ p ^ (e + 1) := by
      simpa using (pow_right_monotone (a := p) (by omega : 1 ≤ p)
        (show 1 ≤ e + 1 by omega))
    omega
  have hpq : p < q := by
    have h₁ : 3 * p ≤ p ^ e * p := Nat.mul_le_mul_right p (hp3.trans hpe)
    rw [pow_succ] at hq_add
    omega
  change IsHyperperfect k (p ^ e * q)
  apply hyperperfect_of_sigma (by dsimp [k]; omega)
  · exact lt_of_lt_of_le (by omega : 1 < p)
      (hpe.trans (Nat.le_mul_of_pos_right _ hq.pos))
  · rw [sigma_prime_power_mul_prime hp hq (ne_of_lt hpq)]
    let s := ∑ i ∈ Finset.range (e + 1), p ^ i
    change k * (s * (q + 1)) + 1 = (k + 1) * (p ^ e * q) + k
    have hg : s * k + 1 = p ^ (e + 1) := by
      simpa only [hp', s] using geom_sum_mul_add k (e + 1)
    have hcalc :
        (k * (s * (q + 1)) + 1) + q = (k + 1) * (p ^ e * q) + k + q := by
      calc
        _ = (s * k + 1) * (q + 1) := by ring
        _ = (k + 1) * (p ^ e * q) + k + q := by
          rw [hg]
          conv_rhs => rw [hp', add_assoc, add_comm k q, hq_add]
          rw [pow_succ]
          ring
    exact Nat.add_right_cancel hcalc

/-- Beyond every bound, either the linear prime pair occurs, or a prime base
and exponent give a prime shift, with at least one of the base and exponent
beyond the bound. The two alternatives may be mixed. -/
def H1 : Prop :=
  ∀ B : ℕ,
    (∃ t : ℕ, B ≤ t ∧ (6 * t + 5).Prime ∧ (12 * t + 13).Prime) ∨
    (∃ p e : ℕ, 3 ≤ p ∧ 1 ≤ e ∧ B ≤ max p e ∧
      p.Prime ∧ (p ^ (e + 1) - (p - 1)).Prime)

/-- The two prime families give hyperperfect numbers of unbounded size
whenever their parameters are unbounded. -/
def H2 : Prop :=
  (∀ t : ℕ, (6 * t + 5).Prime → (12 * t + 13).Prime →
    ∃ n k : ℕ, t ≤ n ∧ 2 ≤ k ∧ IsHyperperfect k n) ∧
  (∀ p e : ℕ, 3 ≤ p → 1 ≤ e → p.Prime → (p ^ (e + 1) - (p - 1)).Prime →
    ∃ n k : ℕ, max p e ≤ n ∧ 2 ≤ k ∧ IsHyperperfect k n)

theorem prime_transfers : H2 := by
  constructor
  · intro t hp hq
    refine ⟨(6 * t + 5) ^ 2 * (12 * t + 13), 4 * t + 3, ?_,
      by omega, linear_pair hp hq⟩
    calc
      t ≤ 6 * t + 5 := by omega
      _ ≤ (6 * t + 5) ^ 2 := by nlinarith
      _ ≤ _ := Nat.le_mul_of_pos_right _ hq.pos
  · intro p e hp3 he hp hq
    refine ⟨p ^ e * (p ^ (e + 1) - (p - 1)), p - 1, ?_,
      by omega, power_shift hp3 he hp hq⟩
    have hpe : p ≤ p ^ e := by
      simpa using (pow_right_monotone (a := p) (by omega : 1 ≤ p) he)
    have exp_le_pow : ∀ m : ℕ, m ≤ p ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ]
          have hpos : 0 < p ^ m := pow_pos hp.pos _
          have hmul : p ^ m * 2 ≤ p ^ m * p := Nat.mul_le_mul_left _ (by omega)
          omega
    exact (max_le hpe (exp_le_pow e)).trans (Nat.le_mul_of_pos_right _ hq.pos)

theorem main : H1 → H2 →
    type_of% @HyperperfectNumber.infinitely_many_hyperperfect_numbers := by
  intro primeFamilies transfer hfinite
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  have witness : ∃ n k : ℕ, N + 1 ≤ n ∧ 2 ≤ k ∧ IsHyperperfect k n := by
    rcases primeFamilies (N + 1) with ⟨t, ht, hp, hq⟩ | ⟨p, e, hp3, he, hB, hp, hq⟩
    · obtain ⟨n, k, hn, hk, h⟩ := transfer.1 t hp hq
      exact ⟨n, k, ht.trans hn, hk, h⟩
    · obtain ⟨n, k, hn, hk, h⟩ := transfer.2 p e hp3 he hp hq
      exact ⟨n, k, hB.trans hn, hk, h⟩
  obtain ⟨n, k, hn, hk, h⟩ := witness
  have hle : n ≤ N := hN ⟨k, hk, h⟩
  omega

end OMA.R_HyperperfectNumber_infinitely_many_hyperperfect_numbers_R1

