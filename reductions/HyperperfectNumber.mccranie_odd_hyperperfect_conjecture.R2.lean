import FormalConjectures.Wikipedia.HyperperfectNumber
import Mathlib

namespace OMA.R_HyperperfectNumber_mccranie_odd_hyperperfect_conjecture_R2

open HyperperfectNumber ArithmeticFunction

-- This refines reduction R1 of the same problem (whose two-prime lemmas are reused below):
-- the new lemmas sigma_prod_lt, abund, small_factor and (in namespace Lib) second_prime_ineq and
-- two_least_three prove abundancy bounds, which narrow both hypotheses to numbers with a small
-- prime factor and, for three prime factors, to finitely many pairs of two least primes per k.

/-- No k-hyperperfect number n with k odd and k > 1 has exactly three distinct prime factors
when its least prime factor p is below 3k and its second least prime factor q satisfies
(p - k - 1)(q - 1) < 3kp (so for each k only finitely many pairs p, q remain, since p > k is odd
and p - k - 1 is at least 1). The side conditions are proved by main for every such n: its prime
factors all exceed k, its divisor sum is 2 mod 4, it has Euler form, and if it has exactly three
prime factors then the two abundancy bounds on p and q hold. -/
def H1 : Prop :=
  ∀ k n : ℕ, Odd k → 1 < k → IsHyperperfect k n → (∀ p : ℕ, p.Prime → p ∣ n → k < p) →
    (∑ d ∈ n.divisors, d) % 4 = 2 →
    (∃ q : ℕ, q.Prime ∧ q % 4 = 1 ∧ n.factorization q % 4 = 1 ∧
      ∀ p : ℕ, p ≠ q → Even (n.factorization p)) →
    (∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
      (∀ r ∈ n.primeFactors, p ≤ r) ∧ (∀ r ∈ n.primeFactors, r ≠ p → q ≤ r) ∧
      p < 3 * k ∧ (p - k - 1) * (q - 1) < 3 * k * p) →
    n.primeFactors.card ≠ 3

/-- No k-hyperperfect number n with k odd and k > 1 has four or more distinct prime factors
(same side conditions as H1, and some prime factor is below (k + 1) times the number of
distinct prime factors). -/
def H2 : Prop :=
  ∀ k n : ℕ, Odd k → 1 < k → IsHyperperfect k n → (∀ p : ℕ, p.Prime → p ∣ n → k < p) →
    (∑ d ∈ n.divisors, d) % 4 = 2 →
    (∃ q : ℕ, q.Prime ∧ q % 4 = 1 ∧ n.factorization q % 4 = 1 ∧
      ∀ p : ℕ, p ≠ q → Even (n.factorization p)) →
    (∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p < n.primeFactors.card * (k + 1)) →
    n.primeFactors.card < 4

/-- The defining equation without truncated subtraction: n + k = 1 + k s(n). -/
lemma hyp_eq {k n : ℕ} (h : IsHyperperfect k n) :
    n + k = 1 + k * ∑ d ∈ n.properDivisors, d := by
  obtain ⟨_, hn, h⟩ := h
  have h1 : 1 ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hn
  have hge : 1 ≤ ∑ d ∈ n.properDivisors, d :=
    Finset.single_le_sum (f := fun d ↦ d) (fun _ _ ↦ Nat.zero_le _) h1
  obtain ⟨t, ht⟩ : ∃ t, ∑ d ∈ n.properDivisors, d = t + 1 :=
    ⟨(∑ d ∈ n.properDivisors, d) - 1, by omega⟩
  rw [ht, Nat.add_sub_cancel] at h
  rw [ht, h]
  ring

/-- `1 + n / p ≤ s(n)` for a prime divisor p of n with n ≠ p. -/
lemma pd_lower {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : 1 < n) (hne : n ≠ p) :
    1 + n / p ≤ ∑ d ∈ n.properDivisors, d := by
  have hsub : ({1, n / p} : Finset ℕ) ⊆ n.properDivisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.mem_properDivisors]
    rcases hd with rfl | rfl
    · exact ⟨one_dvd _, hn⟩
    · exact ⟨Nat.div_dvd_of_dvd hpn, Nat.div_lt_self (by omega) hp.one_lt⟩
  have hne1 : (1 : ℕ) ≠ n / p := by
    intro h
    apply hne
    have := Nat.div_mul_cancel hpn
    rw [← h, one_mul] at this
    exact this.symm
  have hle := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
  rwa [Finset.sum_pair hne1] at hle

/-- Every prime factor p of a k-hyperperfect n with n ≠ p exceeds k. -/
lemma factor_gt {k n p : ℕ} (h : IsHyperperfect k n) (hp : p.Prime) (hpn : p ∣ n)
    (hne : n ≠ p) : k < p := by
  have h1 := hyp_eq h
  have h2 := pd_lower hp hpn h.2.1 hne
  obtain ⟨m, hm⟩ := hpn
  have hmp : n / p = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hp.pos
  rw [hmp] at h2
  by_contra hle
  have hle' : p ≤ k := Nat.le_of_not_lt hle
  have h4 : p * m ≤ k * m := Nat.mul_le_mul_right m hle'
  have h5 : k * (1 + m) ≤ k * ∑ d ∈ n.properDivisors, d := Nat.mul_le_mul_left k h2
  rw [mul_add, mul_one] at h5
  rw [← hm] at h4
  omega

/-- `p ^ a * q ^ b` is neither p nor q. -/
lemma two_primes_ne {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (ha : 0 < a) (hb : 0 < b) :
    p ^ a * q ^ b ≠ p ∧ p ^ a * q ^ b ≠ q := by
  have h1 : p ≤ p ^ a := Nat.le_self_pow ha.ne' p
  have h2 : q ≤ q ^ b := Nat.le_self_pow hb.ne' q
  have h3 := hp.two_le
  have h4 := hq.two_le
  have h5 : p * q ≤ p ^ a * q ^ b := Nat.mul_le_mul h1 h2
  constructor <;> intro h <;> nlinarith

/-- s(p^a q^b) + p^a q^b = σ(p^a) σ(q^b). -/
lemma sum_pd_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a b : ℕ) :
    ∑ d ∈ (p ^ a * q ^ b).properDivisors, d + p ^ a * q ^ b =
      (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) := by
  rw [← Nat.sum_divisors_eq_sum_properDivisors_add_self, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.coprime_pow_primes a b hp hq hpq),
    sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hq]

/-- The hyperperfect equation for p^a q^b: n + k (n + 1) = 1 + k σ(n). -/
lemma master {k p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : IsHyperperfect k (p ^ a * q ^ b)) :
    p ^ a * q ^ b + k * (p ^ a * q ^ b + 1) =
      1 + k * ((∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j)) := by
  rw [← sum_pd_two_primes hp hq hpq a b]
  have h1 := hyp_eq h
  rw [mul_add, mul_add, mul_one]
  omega

/-- The two prime factors of a number with exactly two distinct prime factors. -/
lemma two_factors {n : ℕ} (hn : n ≠ 0) (h : n.primeFactors.card = 2) :
    ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 0 < a ∧ 0 < b ∧ n = p ^ a * q ^ b := by
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp h
  have hp : p ∈ n.primeFactors := by rw [hs]; simp
  have hq : q ∈ n.primeFactors := by rw [hs]; simp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hq' := Nat.prime_of_mem_primeFactors hq
  refine ⟨p, q, n.factorization p, n.factorization q, hp', hq', hpq,
    hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp),
    hq'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hq), ?_⟩
  have := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization, hs, Finset.prod_pair hpq] at this
  exact this.symm

/-- No prime power is hyperperfect. -/
lemma not_prime_pow {k p a : ℕ} (hp : p.Prime) (ha : 0 < a) (h : IsHyperperfect k (p ^ a)) :
    False := by
  have h1 := hyp_eq h
  rw [Nat.sum_properDivisors_prime_nsmul hp] at h1
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  have hs : ∑ x ∈ Finset.range (c + 1), p ^ x = p * (∑ x ∈ Finset.range c, p ^ x) + 1 := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ, mul_comm]
  rw [hs] at h1
  have h2 : p ^ (c + 1) = p * (k * ∑ x ∈ Finset.range c, p ^ x) + 1 := by
    have h3 : k * (p * (∑ x ∈ Finset.range c, p ^ x) + 1) =
        p * (k * ∑ x ∈ Finset.range c, p ^ x) + k := by ring
    omega
  have h4 : p ∣ p * (k * ∑ x ∈ Finset.range c, p ^ x) + 1 := by
    rw [← h2]
    exact dvd_pow_self p (by omega)
  have h5 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p _)).mp h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

/-- For odd p, the geometric sum 1 + p + ... + p^(m-1) has the parity of m. -/
lemma geom_mod_two {p : ℕ} (hp : p % 2 = 1) (m : ℕ) :
    (∑ i ∈ Finset.range m, p ^ i) % 2 = m % 2 := by
  rw [Finset.sum_nat_mod]
  have h : ∀ i ∈ Finset.range m, p ^ i % 2 = 1 := fun i _ => by
    rw [Nat.pow_mod, hp, one_pow, Nat.one_mod]
  rw [Finset.sum_congr rfl h]
  simp

/-- For q = 1 mod 4, the geometric sum 1 + q + ... + q^(m-1) is m mod 4. -/
lemma geom_mod_four {q : ℕ} (hq : q % 4 = 1) (m : ℕ) :
    (∑ j ∈ Finset.range m, q ^ j) % 4 = m % 4 := by
  rw [Finset.sum_nat_mod]
  have h : ∀ j ∈ Finset.range m, q ^ j % 4 = 1 := fun j _ => by
    rw [Nat.pow_mod, hq, one_pow, Nat.one_mod]
  rw [Finset.sum_congr rfl h]
  simp

/-- For q = 3 mod 4, the geometric sum with an even number of terms is 0 mod 4. -/
lemma geom_mod_four_three {q : ℕ} (hq : q % 4 = 3) (m : ℕ) :
    (∑ j ∈ Finset.range (2 * m), q ^ j) % 4 = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      pow_succ q (2 * m)]
    have h2 : (q ^ (2 * m) * q) % 4 = (q ^ (2 * m) % 4) * 3 % 4 := by rw [Nat.mul_mod, hq]
    have h3 : q ^ (2 * m) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    omega

/-- If A B = 2 mod 4, one factor is odd and the other is 2 mod 4. -/
lemma mod4_split {A B : ℕ} (h : (A * B) % 4 = 2) :
    (A % 2 = 1 ∧ B % 4 = 2) ∨ (A % 4 = 2 ∧ B % 2 = 1) := by
  have h1 := Nat.mul_mod A B 4
  rcases (show A % 4 = 0 ∨ A % 4 = 1 ∨ A % 4 = 2 ∨ A % 4 = 3 by omega) with h3 | h3 | h3 | h3 <;>
  rcases (show B % 4 = 0 ∨ B % 4 = 1 ∨ B % 4 = 2 ∨ B % 4 = 3 by omega) with h4 | h4 | h4 | h4 <;>
  rw [h3, h4] at h1 <;> omega

/-- For odd q and odd b, σ(q^b) = 2 mod 4 forces q = 1 mod 4 and b = 1 mod 4. -/
lemma odd_exp_mod4 {q b : ℕ} (hq2 : q % 2 = 1) (hb : Odd b)
    (hB : (∑ j ∈ Finset.range (b + 1), q ^ j) % 4 = 2) : q % 4 = 1 ∧ b % 4 = 1 := by
  obtain ⟨c, rfl⟩ := hb
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by omega) with h | h
  · rw [geom_mod_four h] at hB
    omega
  · have := geom_mod_four_three h (c + 1)
    rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring] at this
    omega

/-- For odd k and odd n, n - 1 + k (n + 1) is 2 mod 4, so a k-hyperperfect p^a q^b has
σ(p^a) σ(q^b) = 2 mod 4. -/
lemma sigma_prod_mod4 {k p q a b : ℕ} (hk_odd : Odd k) (hp2 : p % 2 = 1) (hq2 : q % 2 = 1)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : IsHyperperfect k (p ^ a * q ^ b)) :
    ((∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j)) % 4 = 2 := by
  have hm := master hp hq hpq h
  have hN : (p ^ a * q ^ b) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod, hp2, Nat.pow_mod q, hq2]
    simp
  generalize p ^ a * q ^ b = N at hm hN
  generalize (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) = M at hm ⊢
  obtain ⟨u, rfl⟩ : ∃ u, N = 2 * u + 1 := ⟨N / 2, by omega⟩
  obtain ⟨z, rfl⟩ := hk_odd
  ring_nf at hm
  have hM2 : M % 2 = 0 := by omega
  obtain ⟨m, rfl⟩ : ∃ m, M = 2 * m := ⟨M / 2, by omega⟩
  ring_nf at hm
  omega

/-- The shape of a two-prime k-hyperperfect p^a q^b (k odd, k > 1): exactly one exponent is
odd, and that exponent and its prime are both 1 mod 4. -/
lemma shape {k p q a b : ℕ} (hk_odd : Odd k) (hk : 1 < k) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (ha0 : 0 < a) (hb0 : 0 < b)
    (h : IsHyperperfect k (p ^ a * q ^ b)) :
    (Even a ∧ Odd b ∧ q % 4 = 1 ∧ b % 4 = 1) ∨ (Odd a ∧ Even b ∧ p % 4 = 1 ∧ a % 4 = 1) := by
  have hne := two_primes_ne hp hq ha0 hb0
  have hkp : k < p := factor_gt h hp (Dvd.dvd.mul_right (dvd_pow_self p ha0.ne') _) hne.1
  have hkq : k < q := factor_gt h hq (Dvd.dvd.mul_left (dvd_pow_self q hb0.ne') _) hne.2
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  have hs := sigma_prod_mod4 hk_odd hp2 hq2 hp hq hpq h
  have hA := geom_mod_two hp2 (a + 1)
  have hB := geom_mod_two hq2 (b + 1)
  rcases mod4_split hs with ⟨hA1, hB2⟩ | ⟨hA2, hB1⟩
  · have hae : Even a := Nat.even_iff.mpr (by omega)
    have hbo : Odd b := Nat.odd_iff.mpr (by omega)
    exact Or.inl ⟨hae, hbo, odd_exp_mod4 hq2 hbo hB2⟩
  · have hao : Odd a := Nat.odd_iff.mpr (by omega)
    have hbe : Even b := Nat.even_iff.mpr (by omega)
    exact Or.inr ⟨hao, hbe, odd_exp_mod4 hp2 hao hA2⟩

/-- The two-prime classification: if p ^ 2 q is k-hyperperfect (k odd, k > 1), then
2 p = 3 k + 1 and q = 3 k + 4. -/
lemma p2q_classify {k p q : ℕ} (hk_odd : Odd k) (hk : 1 < k) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (h : IsHyperperfect k (p ^ 2 * q ^ 1)) : 2 * p = 3 * k + 1 ∧ q = 3 * k + 4 := by
  have hm := master hp hq hpq h
  have hne := two_primes_ne hp hq two_pos one_pos
  have hkp : k < p := factor_gt h hp (Dvd.dvd.mul_right (dvd_pow_self p two_ne_zero) _) hne.1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hm
  have hq2 := hq.two_le
  obtain ⟨c, hc⟩ := hk_odd
  obtain ⟨m, hmp⟩ := hp.odd_of_ne_two (by omega)
  have E : (p : ℤ) ^ 2 * q = 1 + k * (p + 1) * (p + q) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hm
    push_cast at this
    linear_combination this
  have hdpq : ((p : ℤ) ^ 2 - k * (p + 1)) * (p + q) = (p + 1) * (p ^ 2 - p + 1) := by
    linear_combination E
  have hcop : IsCoprime ((p : ℤ) ^ 2 - k * (p + 1)) ((p : ℤ) + 1) :=
    ⟨1, (k : ℤ) - p + 1, by ring⟩
  have hdvd : ((p : ℤ) ^ 2 - k * (p + 1)) ∣ ((p : ℤ) + 1) * ((p : ℤ) ^ 2 - p + 1) :=
    ⟨(p : ℤ) + q, hdpq.symm⟩
  obtain ⟨e, he⟩ := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨i, hi⟩ : ∃ i : ℤ, i = p - 1 - k := ⟨_, rfl⟩
  have hi0 : 0 ≤ i := by omega
  have hd : (p : ℤ) ^ 2 - k * (p + 1) = 1 + i * (p + 1) := by rw [hi]; ring
  have hqe : (p : ℤ) + q = (p + 1) * e := by
    have hd0 : (p : ℤ) ^ 2 - k * (p + 1) ≠ 0 := by
      rw [hd]
      nlinarith
    apply mul_left_cancel₀ hd0
    linear_combination hdpq + (p + 1) * he
  have he0 : 0 < e := by nlinarith
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = p - 2 - i * e := ⟨_, rfl⟩
  have hej : e = 3 + j * (p + 1) := by
    rw [hj, hi]
    linear_combination (-1 : ℤ) * he
  have hj0 : 0 ≤ j := by
    by_contra hneg
    have hneg' : j + 1 ≤ 0 := by omega
    nlinarith
  have he' : (p : ℤ) ^ 2 - p + 1 = (1 + i * (p + 1)) * (3 + j * (p + 1)) := by
    rw [← hd, ← hej]
    exact he
  have key : (i * j) * (p + 1) = p - 2 - j - 3 * i := by
    have hp1 : ((p : ℤ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hp1
    linear_combination (-1 : ℤ) * he'
  have hij : i * j = 0 := by
    have h0 : 0 ≤ i * j := mul_nonneg hi0 hj0
    by_contra hne0
    have h1 : 1 ≤ i * j := by omega
    nlinarith
  rcases mul_eq_zero.mp hij with h0 | h0
  · exfalso
    omega
  · rw [h0] at hej key
    have he3 : e = 3 := by linarith
    rw [he3] at hqe
    constructor <;> omega

/-- Final size step: P < (2k+1)(k+1)(p-1) with k + 2 ≤ p gives P < 2 p^3. -/
lemma core_final {p k P : ℤ} (hp : 3 ≤ p) (hk : 1 ≤ k) (hkp : k + 2 ≤ p)
    (hP : P < (2 * k + 1) * (k + 1) * (p - 1)) : P < 2 * p ^ 3 := by
  have h1 : (2 * k + 1) * (k + 1) ≤ (2 * p - 3) * (p - 1) := by nlinarith
  have h2 : (2 * k + 1) * (k + 1) * (p - 1) ≤ (2 * p - 3) * (p - 1) * (p - 1) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  nlinarith

/-- Case S_q ≥ 2 (p-1)(k+1): P ≤ (2k+1) q. -/
lemma core_case_big {p q k P Sq G X Y : ℤ} (hp : 3 ≤ p) (hq : 0 < q)
    (hP0 : 0 < P) (hSq0 : 0 < Sq) (hG : 1 ≤ G)
    (hX : X = Sq * G - (p - 1) * (k + 1)) (hY : Y = k * Sq + (p - 1) * (k - 1))
    (hStar : P * X = q * Y) (hc : 2 * (p - 1) * (k + 1) ≤ Sq) : P ≤ (2 * k + 1) * q := by
  have hSG : Sq ≤ Sq * G := by nlinarith
  have h2X : Sq ≤ 2 * X := by rw [hX]; nlinarith
  have h1 : P * Sq ≤ P * (2 * X) := mul_le_mul_of_nonneg_left h2X hP0.le
  have h3 : 2 * (p - 1) * (k - 1) ≤ Sq := by nlinarith
  have h4 : q * (2 * (p - 1) * (k - 1)) ≤ q * Sq := mul_le_mul_of_nonneg_left h3 hq.le
  have h5 : P * Sq ≤ (2 * k + 1) * q * Sq := by
    rw [hY] at hStar
    nlinarith
  exact le_of_mul_le_mul_right h5 hSq0

/-- The two-prime size bound in free variables: with P = 1 + (p-1) R = p^a, q^b = 1 + (q-1) T,
σ(p^a) = 1 + p R, σ(q^b) = 1 + q T and the hyperperfect equation, P < 2 p^3. Put
D = P - k R, F = (1 + k) P - q D, G = (k + 1)(p - 1) - q (p - 1 - k). Then
σ(q^b) F = (1 + k) P + (k - 1) q, (p - 1) F + q k = P G and P X = q Y with
X = σ(q^b) G - (p - 1)(k + 1), Y = k σ(q^b) + (p - 1)(k - 1). -/
lemma core_bound {p q k R T : ℤ} (hp : 3 ≤ p) (hk : 1 ≤ k) (hkp : k + 2 ≤ p)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hq : 0 < q)
    (hm : (1 + (p - 1) * R) * (1 + (q - 1) * T) + k * ((1 + (p - 1) * R) * (1 + (q - 1) * T) + 1) =
      1 + k * ((1 + p * R) * (1 + q * T)))
    (hcop : IsCoprime (1 + (p - 1) * R) q) : 1 + (p - 1) * R < 2 * p ^ 3 := by
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = 1 + (p - 1) * R := ⟨_, rfl⟩
  obtain ⟨Sq, hSq⟩ : ∃ Sq : ℤ, Sq = 1 + q * T := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℤ, F = (1 + k) * P - q * (P - k * R) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℤ, G = (k + 1) * (p - 1) - q * (p - 1 - k) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = Sq * G - (p - 1) * (k + 1) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = k * Sq + (p - 1) * (k - 1) := ⟨_, rfl⟩
  rw [← hP] at hcop ⊢
  have hB : Sq * F = (1 + k) * P + (k - 1) * q := by
    rw [hSq, hF, hP]
    linear_combination (-q) * hm
  have hA : (p - 1) * F + q * k = P * G := by
    rw [hF, hG, hP]
    ring
  have hStar : P * X = q * Y := by
    rw [hX, hY, hSq, hG, hP]
    linear_combination (-(q * (p - 1))) * hm
  have hP0 : 0 < P := by
    rw [hP]
    nlinarith
  have hSq0 : 0 < Sq := by
    rw [hSq]
    nlinarith
  have hF0 : 0 < F := by
    by_contra hcon
    have h1 : Sq * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hSq0.le (not_lt.mp hcon)
    nlinarith
  have hG0 : 1 ≤ G := by
    by_contra hcon
    have h1 : P * G ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP0.le (by omega)
    have h2 : 0 < (p - 1) * F := mul_pos (by linarith) hF0
    nlinarith
  have hqb : q < (k + 1) * (p - 1) := by
    have h1 : q ≤ q * (p - 1 - k) := le_mul_of_one_le_right (by linarith) (by linarith)
    rw [hG] at hG0
    linarith
  have hY0 : 0 < Y := by
    rw [hY]
    nlinarith
  have hdvd : P ∣ Y := hcop.dvd_of_dvd_mul_left ⟨X, by linarith⟩
  have hPY : P ≤ Y := Int.le_of_dvd hY0 hdvd
  have hbound : P < (2 * k + 1) * (k + 1) * (p - 1) := by
    by_cases hc : 2 * (p - 1) * (k + 1) ≤ Sq
    · have h1 := core_case_big hp hq hP0 hSq0 hG0 hX hY hStar hc
      have h2 : (2 * k + 1) * q < (2 * k + 1) * ((k + 1) * (p - 1)) :=
        mul_lt_mul_of_pos_left hqb (by linarith)
      linarith
    · have hc' : Sq < 2 * (p - 1) * (k + 1) := not_le.mp hc
      have h1 : k * Sq ≤ k * (2 * (p - 1) * (k + 1)) := mul_le_mul_of_nonneg_left hc'.le (by linarith)
      rw [hY] at hPY
      nlinarith
  exact core_final hp hk hkp hbound

/-- `1 + p (1 + ... + p^(a-1)) = 1 + p + ... + p^a`. -/
lemma geom_succ (p a : ℕ) :
    ∑ i ∈ Finset.range (a + 1), p ^ i = 1 + p * ∑ i ∈ Finset.range a, p ^ i := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- In a two-prime k-hyperperfect p^a q^b (k odd, k > 1), the exponent a is at most 3. -/
lemma exp_le_three {k p q a b : ℕ} (hk_odd : Odd k) (hk : 1 < k) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha0 : 0 < a) (hb0 : 0 < b) (h : IsHyperperfect k (p ^ a * q ^ b)) : a ≤ 3 := by
  have hm := master hp hq hpq h
  have hne := two_primes_ne hp hq ha0 hb0
  have hkp : k < p := factor_gt h hp (Dvd.dvd.mul_right (dvd_pow_self p ha0.ne') _) hne.1
  have hkq : k < q := factor_gt h hq (Dvd.dvd.mul_left (dvd_pow_self q hb0.ne') _) hne.2
  obtain ⟨x, hx⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨z, hz⟩ := hk_odd
  rw [geom_succ p a, geom_succ q b] at hm
  have hPg : (p : ℤ) ^ a = 1 + (p - 1) * ((∑ i ∈ Finset.range a, p ^ i : ℕ) : ℤ) := by
    have := geom_sum_mul (p : ℤ) a
    push_cast
    linear_combination (-1 : ℤ) * this
  have hQg : (q : ℤ) ^ b = 1 + (q - 1) * ((∑ j ∈ Finset.range b, q ^ j : ℕ) : ℤ) := by
    have := geom_sum_mul (q : ℤ) b
    push_cast
    linear_combination (-1 : ℤ) * this
  have hm' := congrArg (Nat.cast : ℕ → ℤ) hm
  generalize hR : ∑ i ∈ Finset.range a, p ^ i = R at hm' hPg
  generalize hT : ∑ j ∈ Finset.range b, q ^ j = T at hm' hQg
  push_cast at hm'
  rw [hPg, hQg] at hm'
  have hcop : IsCoprime (1 + ((p : ℤ) - 1) * R) (q : ℤ) := by
    rw [← hPg]
    have := Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow_left a ((Nat.coprime_primes hp hq).mpr hpq))
    push_cast at this
    exact this
  have hb := core_bound (p := (p : ℤ)) (q := (q : ℤ)) (k := (k : ℤ)) (R := (R : ℤ)) (T := (T : ℤ))
    (by omega) (by omega) (by omega) (by positivity) (by positivity) (by exact_mod_cast hq.pos)
    hm' hcop
  rw [← hPg] at hb
  by_contra hcon
  have ha4 : 4 ≤ a := by omega
  have h1 : (p : ℤ) ^ 4 ≤ (p : ℤ) ^ a := pow_le_pow_right₀ (by norm_cast; omega) ha4
  have h3 : (3 : ℤ) * p ^ 3 ≤ p * p ^ 3 :=
    mul_le_mul_of_nonneg_right (by norm_cast; omega) (by positivity)
  have h4 : (p : ℤ) ^ 4 = p * p ^ 3 := by ring
  have h5 : (0 : ℤ) < p ^ 3 := by
    have : (0 : ℤ) < p := by exact_mod_cast hp.pos
    positivity
  linarith

/-- The hyperperfect equation in the form n + k (n + 1) = 1 + k σ(n). -/
lemma general_eq {k n : ℕ} (h : IsHyperperfect k n) :
    n + k * (n + 1) = 1 + k * ∑ d ∈ n.divisors, d := by
  have h1 := hyp_eq h
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, mul_add, mul_add, mul_one]
  omega

/-- Every prime factor of a k-hyperperfect n exceeds k. -/
lemma all_factors_gt {k n : ℕ} (h : IsHyperperfect k n) :
    ∀ p : ℕ, p.Prime → p ∣ n → k < p := by
  intro p hp hpn
  apply factor_gt h hp hpn
  rintro rfl
  exact not_prime_pow hp one_pos (by rwa [pow_one])

/-- For odd k > 1, a k-hyperperfect n is odd and σ(n) = 2 mod 4. -/
lemma sigma_mod4_general {k n : ℕ} (hk_odd : Odd k) (hk : 1 < k) (h : IsHyperperfect k n) :
    (∑ d ∈ n.divisors, d) % 4 = 2 := by
  have hm := general_eq h
  have hn2 : n % 2 = 1 := by
    by_contra hcon
    have h2 : 2 ∣ n := by omega
    have := all_factors_gt h 2 Nat.prime_two h2
    omega
  generalize ∑ d ∈ n.divisors, d = M at hm ⊢
  obtain ⟨u, rfl⟩ : ∃ u, n = 2 * u + 1 := ⟨n / 2, by omega⟩
  obtain ⟨z, rfl⟩ := hk_odd
  ring_nf at hm
  have hM2 : M % 2 = 0 := by omega
  obtain ⟨m, rfl⟩ : ∃ m, M = 2 * m := ⟨M / 2, by omega⟩
  ring_nf at hm
  omega

/-- If a product is odd, every factor is odd. -/
lemma prod_odd_each {s : Finset ℕ} {g : ℕ → ℕ} (h : (∏ x ∈ s, g x) % 2 = 1) {y : ℕ} (hy : y ∈ s) :
    g y % 2 = 1 := by
  by_contra hcon
  have h2 : 2 ∣ g y := by omega
  have h3 : 2 ∣ ∏ x ∈ s, g x := dvd_trans h2 (Finset.dvd_prod_of_mem g hy)
  omega

/-- If a product is 2 mod 4, one factor is 2 mod 4 and all the others are odd. -/
lemma prod_mod4_two {s : Finset ℕ} {g : ℕ → ℕ} (h : (∏ x ∈ s, g x) % 4 = 2) :
    ∃ x ∈ s, g x % 4 = 2 ∧ ∀ y ∈ s, y ≠ x → g y % 2 = 1 := by
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases mod4_split h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨x, hx, hx2, hy⟩ := ih h2
      refine ⟨x, Finset.mem_insert_of_mem hx, hx2, ?_⟩
      intro y hy' hyx
      rcases Finset.mem_insert.mp hy' with rfl | hys
      · exact h1
      · exact hy y hys hyx
    · refine ⟨a, Finset.mem_insert_self a s, h1, ?_⟩
      intro y hy' hya
      rcases Finset.mem_insert.mp hy' with rfl | hys
      · exact absurd rfl hya
      · exact prod_odd_each h2 hys

/-- Euler form: for odd k > 1, a k-hyperperfect n has exactly one prime q with odd exponent,
and q = 1 mod 4, with exponent = 1 mod 4. -/
lemma euler_form {k n : ℕ} (hk_odd : Odd k) (hk : 1 < k) (h : IsHyperperfect k n) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 1 ∧ n.factorization q % 4 = 1 ∧
      ∀ p : ℕ, p ≠ q → Even (n.factorization p) := by
  have hn0 : n ≠ 0 := by
    have := h.2.1
    omega
  have hσ := sigma_mod4_general hk_odd hk h
  have hprod : ∑ d ∈ n.divisors, d =
      ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    rw [← sigma_one_apply,
      IsMultiplicative.multiplicative_factorization (ArithmeticFunction.sigma 1)
        isMultiplicative_sigma hn0, Finsupp.prod, Nat.support_factorization]
    apply Finset.prod_congr rfl
    intro p hp
    exact sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)
  rw [hprod] at hσ
  obtain ⟨q, hq, hq2, hother⟩ := prod_mod4_two hσ
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hodd : ∀ p, p.Prime → p ∣ n → p % 2 = 1 := fun p hp hpn => by
    have := all_factors_gt h p hp hpn
    exact Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hq_odd := hodd q hqp (Nat.dvd_of_mem_primeFactors hq)
  have hvq : Odd (n.factorization q) := by
    have := geom_mod_two hq_odd (n.factorization q + 1)
    exact Nat.odd_iff.mpr (by omega)
  obtain ⟨hq4, hv4⟩ := odd_exp_mod4 hq_odd hvq hq2
  refine ⟨q, hqp, hq4, hv4, ?_⟩
  intro p hpq
  by_cases hp : p ∈ n.primeFactors
  · have h1 := hother p hp hpq
    have h2 := geom_mod_two (hodd p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)) (n.factorization p + 1)
    exact Nat.even_iff.mpr (by omega)
  · have h0 : n.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    rw [h0]
    exact ⟨0, rfl⟩

/-- `(1 + p + ... + p^(m-1)) (p - 1) + 1 = p^m`. -/
lemma geom_pred_mul {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    (∑ i ∈ Finset.range m, p ^ i) * (p - 1) + 1 = p ^ m := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, add_mul, pow_succ]
    nlinarith [ih]

/-- Abundancy upper bound: σ(n) ∏ (p - 1) < n ∏ p over the prime factors of n. -/
lemma sigma_prod_lt {n : ℕ} (hn : 1 < n) :
    (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1) < n * ∏ p ∈ n.primeFactors, p := by
  have hn0 : n ≠ 0 := by omega
  have hprod : ∑ d ∈ n.divisors, d =
      ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    rw [← sigma_one_apply,
      IsMultiplicative.multiplicative_factorization (ArithmeticFunction.sigma 1)
        isMultiplicative_sigma hn0, Finsupp.prod, Nat.support_factorization]
    apply Finset.prod_congr rfl
    intro p hp
    exact sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)
  have hnp : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    have := Nat.prod_factorization_pow_eq_self hn0
    rw [Finsupp.prod, Nat.support_factorization] at this
    exact this.symm
  have hne : n.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    exact hn
  rw [show n * ∏ p ∈ n.primeFactors, p =
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) * ∏ p ∈ n.primeFactors, p from by
    rw [← hnp]]
  rw [hprod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_lt_prod_of_nonempty _ _ hne
  · intro p hp
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : 1 ≤ ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
      rw [Finset.sum_range_succ']
      simp
    exact Nat.mul_pos (by omega) (by omega)
  · intro p hp
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have := geom_pred_mul (p := p) (by omega) (n.factorization p + 1)
    rw [pow_succ] at this
    omega

/-- For a k-hyperperfect n with k > 1: (k + 1) ∏ (p - 1) < k ∏ p over the prime factors. -/
lemma abund {k n : ℕ} (hk : 1 < k) (h : IsHyperperfect k n) :
    (k + 1) * ∏ p ∈ n.primeFactors, (p - 1) < k * ∏ p ∈ n.primeFactors, p := by
  have hn := h.2.1
  have hm := general_eq h
  have hlt := sigma_prod_lt hn
  generalize ∑ d ∈ n.divisors, d = S at hm hlt
  generalize ∏ p ∈ n.primeFactors, (p - 1) = A at hlt ⊢
  generalize ∏ p ∈ n.primeFactors, p = B at hlt ⊢
  have h1 : (k + 1) * n < k * S := by nlinarith
  have h2 : (k + 1) * n * A ≤ k * S * A := Nat.mul_le_mul_right A h1.le
  have h3 : k * (S * A) < k * (n * B) := Nat.mul_lt_mul_of_pos_left hlt (by omega)
  have h4 : n * ((k + 1) * A) < n * (k * B) := by
    have e1 : n * ((k + 1) * A) = (k + 1) * n * A := by ring
    have e2 : n * (k * B) = k * (n * B) := by ring
    have e3 : k * S * A = k * (S * A) := by ring
    rw [e1, e2]
    omega
  exact Nat.lt_of_mul_lt_mul_left h4

/-- Integer Weierstrass-type bound: if every element of s is at least B, then
B ∏ (p - 1) ≥ (B - card s) ∏ p. -/
lemma weier {s : Finset ℕ} {B : ℤ} (hB : 1 ≤ B) (h : ∀ p ∈ s, B ≤ (p : ℤ)) :
    (B - s.card) * ∏ p ∈ s, (p : ℤ) ≤ B * ∏ p ∈ s, ((p : ℤ) - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
    have haB := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hP : 0 ≤ ∏ p ∈ s, (p : ℤ) := Finset.prod_nonneg (fun p _ => by positivity)
    have hc : (0 : ℤ) ≤ s.card := by positivity
    have h1 : ((a : ℤ) - 1) * ((B - s.card) * ∏ p ∈ s, (p : ℤ)) ≤
        ((a : ℤ) - 1) * (B * ∏ p ∈ s, ((p : ℤ) - 1)) :=
      mul_le_mul_of_nonneg_left ih' (by nlinarith)
    have h2 : (B - ((s.card + 1 : ℕ) : ℤ)) * a ≤ ((a : ℤ) - 1) * (B - s.card) := by
      push_cast
      nlinarith
    have h3 : (B - ((s.card + 1 : ℕ) : ℤ)) * a * ∏ p ∈ s, (p : ℤ) ≤
        ((a : ℤ) - 1) * (B - s.card) * ∏ p ∈ s, (p : ℤ) :=
      mul_le_mul_of_nonneg_right h2 hP
    calc (B - ((s.card + 1 : ℕ) : ℤ)) * ((a : ℤ) * ∏ p ∈ s, (p : ℤ))
        = (B - ((s.card + 1 : ℕ) : ℤ)) * a * ∏ p ∈ s, (p : ℤ) := by ring
      _ ≤ ((a : ℤ) - 1) * (B - s.card) * ∏ p ∈ s, (p : ℤ) := h3
      _ = ((a : ℤ) - 1) * ((B - s.card) * ∏ p ∈ s, (p : ℤ)) := by ring
      _ ≤ ((a : ℤ) - 1) * (B * ∏ p ∈ s, ((p : ℤ) - 1)) := h1
      _ = B * (((a : ℤ) - 1) * ∏ p ∈ s, ((p : ℤ) - 1)) := by ring

/-- Casting ∏ (p - 1) over prime factors to ℤ. -/
lemma cast_prod_pred {n : ℕ} :
    ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℤ) = ∏ p ∈ n.primeFactors, ((p : ℤ) - 1) := by
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have := (Nat.prime_of_mem_primeFactors hp).one_le
  push_cast [Nat.cast_sub this]
  rfl

/-- Some prime factor of a k-hyperperfect n (k > 1) is below (k + 1) times the number of
distinct prime factors. -/
lemma small_factor {k n : ℕ} (hk : 1 < k) (h : IsHyperperfect k n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p < n.primeFactors.card * (k + 1) := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ p ∈ n.primeFactors, ((n.primeFactors.card * (k + 1) : ℕ) : ℤ) ≤ (p : ℤ) :=
    fun p hp => by
      exact_mod_cast hcon p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hne : n.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    exact h.2.1
  have hc0 : 0 < n.primeFactors.card := Finset.card_pos.mpr hne
  have hw := weier (by push_cast; nlinarith) hall
  have ha := abund hk h
  have ha' : ((k + 1 : ℕ) : ℤ) * ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℤ) <
      (k : ℤ) * ((∏ p ∈ n.primeFactors, p : ℕ) : ℤ) := by exact_mod_cast ha
  rw [cast_prod_pred] at ha'
  push_cast at ha' hw
  generalize ∏ p ∈ n.primeFactors, ((p : ℤ) - 1) = A at ha' hw
  generalize ∏ p ∈ n.primeFactors, (p : ℤ) = P at ha' hw
  have hm0 : (0 : ℤ) < n.primeFactors.card := by exact_mod_cast hc0
  generalize (n.primeFactors.card : ℤ) = m at ha' hw hm0
  have : m * ((k + 1) * A) ≥ m * (k * P) := by nlinarith
  have := le_of_mul_le_mul_left this hm0
  linarith

/-- If a k-hyperperfect n (k odd, k > 1) has exactly three distinct prime factors, one of them
is below 3k. -/
lemma small_factor_three {k n : ℕ} (hk_odd : Odd k) (hk : 1 < k) (h : IsHyperperfect k n)
    (h3 : n.primeFactors.card = 3) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p < 3 * k := by
  by_contra hcon
  push Not at hcon
  have hbig : ∀ p ∈ n.primeFactors, 3 * k + 2 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have h1 := hcon p hpp hpn
    have h2 := all_factors_gt h p hpp hpn
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two (by omega))
    have hk2 : k % 2 = 1 := Nat.odd_iff.mp hk_odd
    have hne : p ≠ 3 * k := by
      rintro rfl
      rw [Nat.prime_mul_iff] at hpp
      rcases hpp with ⟨_, hk1⟩ | ⟨_, hk1⟩ <;> omega
    omega
  have ha := abund hk h
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Finset.card_eq_three.mp h3
  have hx := hbig x (by rw [hs]; simp)
  have hy := hbig y (by rw [hs]; simp)
  have hz := hbig z (by rw [hs]; simp)
  rw [hs, Finset.prod_insert (by simp [hxy, hxz]), Finset.prod_insert (by simp [hyz]),
    Finset.prod_singleton, Finset.prod_insert (by simp [hxy, hxz]),
    Finset.prod_insert (by simp [hyz]), Finset.prod_singleton] at ha
  have ha' : ((k : ℤ) + 1) * (((x : ℤ) - 1) * (((y : ℤ) - 1) * ((z : ℤ) - 1))) <
      (k : ℤ) * ((x : ℤ) * ((y : ℤ) * (z : ℤ))) := by
    have := ha
    zify [show 1 ≤ x by omega, show 1 ≤ y by omega, show 1 ≤ z by omega] at this
    exact this
  have hx' : (3 * (k : ℤ) + 2) ≤ x := by exact_mod_cast hx
  have hy' : (3 * (k : ℤ) + 2) ≤ y := by exact_mod_cast hy
  have hz' : (3 * (k : ℤ) + 2) ≤ z := by exact_mod_cast hz
  have hk' : (1 : ℤ) < k := by exact_mod_cast hk
  generalize (x : ℤ) = X at ha' hx'
  generalize (y : ℤ) = Y at ha' hy'
  generalize (z : ℤ) = Z at ha' hz'
  generalize (k : ℤ) = K at ha' hx' hy' hz' hk'
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = 3 * K + 2 := ⟨_, rfl⟩
  rw [← hB] at hx' hy' hz'
  have e1 : (X - 1) * B ≥ X * (B - 1) := by nlinarith
  have e2 : (Y - 1) * B ≥ Y * (B - 1) := by nlinarith
  have e3 : (Z - 1) * B ≥ Z * (B - 1) := by nlinarith
  have hB1 : 0 ≤ B - 1 := by omega
  have hX0 : 0 < X := by omega
  have hY0 : 0 < Y := by omega
  have hZ0 : 0 < Z := by omega
  have f1 : ((X - 1) * B) * ((Y - 1) * B) ≥ (X * (B - 1)) * (Y * (B - 1)) :=
    mul_le_mul e1 e2 (mul_nonneg (by omega) hB1) (mul_nonneg (by omega) (by omega))
  have f2 : ((X - 1) * B) * ((Y - 1) * B) * ((Z - 1) * B) ≥
      (X * (B - 1)) * (Y * (B - 1)) * (Z * (B - 1)) :=
    mul_le_mul f1 e3 (mul_nonneg (by omega) hB1)
      (mul_nonneg (mul_nonneg (by omega) (by omega)) (mul_nonneg (by omega) (by omega)))
  have f3 : ((X - 1) * (Y - 1) * (Z - 1)) * B ^ 3 ≥ (X * Y * Z) * (B - 1) ^ 3 := by
    have e4 : ((X - 1) * B) * ((Y - 1) * B) * ((Z - 1) * B) =
        ((X - 1) * (Y - 1) * (Z - 1)) * B ^ 3 := by ring
    have e5 : (X * (B - 1)) * (Y * (B - 1)) * (Z * (B - 1)) = (X * Y * Z) * (B - 1) ^ 3 := by
      ring
    rw [← e4, ← e5]
    exact f2
  have g : (K + 1) * (B - 1) ^ 3 > K * B ^ 3 := by rw [hB]; nlinarith
  have hXYZ : 0 < X * Y * Z := by positivity
  have h1 : (K + 1) * (((X - 1) * (Y - 1) * (Z - 1)) * B ^ 3) ≥
      (K + 1) * ((X * Y * Z) * (B - 1) ^ 3) :=
    mul_le_mul_of_nonneg_left f3 (by omega)
  have h2 : (K + 1) * (B - 1) ^ 3 * (X * Y * Z) > K * B ^ 3 * (X * Y * Z) :=
    mul_lt_mul_of_pos_right g hXYZ
  have hB3 : 0 < B ^ 3 := pow_pos (by omega) 3
  have h3 := mul_lt_mul_of_pos_right ha' hB3
  have e6 : (K + 1) * ((X - 1) * ((Y - 1) * (Z - 1))) * B ^ 3 =
      (K + 1) * (((X - 1) * (Y - 1) * (Z - 1)) * B ^ 3) := by ring
  have e7 : K * (X * (Y * Z)) * B ^ 3 = K * B ^ 3 * (X * Y * Z) := by ring
  have e8 : (K + 1) * ((X * Y * Z) * (B - 1) ^ 3) = (K + 1) * (B - 1) ^ 3 * (X * Y * Z) := by
    ring
  rw [e6, e7] at h3
  rw [e8] at h1
  linarith

namespace Lib

/-- k σ(n) = (k + 1) n + (k - 1), written without subtraction. -/
lemma sigma_eq {k n : ℕ} (h : IsHyperperfect k n) :
    k * (∑ d ∈ n.divisors, d) + 1 = (k + 1) * n + k := by
  have := general_eq h
  linarith

/-- Hyperperfect numbers are abundant in the sense (k + 1) n < k σ(n) when k > 1. -/
lemma sigma_gt {k n : ℕ} (hk : 1 < k) (h : IsHyperperfect k n) :
    (k + 1) * n < k * ∑ d ∈ n.divisors, d := by
  have := sigma_eq h
  omega

/-- σ(n) as a product over prime factors. -/
lemma sigma_prod {n : ℕ} (hn0 : n ≠ 0) :
    ∑ d ∈ n.divisors, d =
      ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
  rw [← sigma_one_apply,
    IsMultiplicative.multiplicative_factorization (ArithmeticFunction.sigma 1)
      isMultiplicative_sigma hn0, Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  exact sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)

/-- n as a product over prime factors. -/
lemma n_prod {n : ℕ} (hn0 : n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  have := Nat.prod_factorization_pow_eq_self hn0
  rw [Finsupp.prod, Nat.support_factorization] at this
  exact this.symm

/-- σ(p^a) (p - 1) + 1 = p^(a+1) for p ≥ 1. -/
lemma geom_pred_mul {p : ℕ} (hp : 1 ≤ p) (a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) := by
  have := geom_sum_mul_add (p - 1) (a + 1)
  rwa [Nat.sub_add_cancel hp] at this

/-- σ(n) ∏ (p - 1) < n ∏ p over the prime factors, for n > 1. -/
lemma sigma_mul_prod_lt {n : ℕ} (hn : 1 < n) :
    (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1) <
      n * ∏ p ∈ n.primeFactors, p := by
  have hn0 : n ≠ 0 := by omega
  have e : n * ∏ p ∈ n.primeFactors, p =
      ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) := by
    rw [Finset.prod_mul_distrib, ← n_prod hn0]
  rw [e, sigma_prod hn0, ← Finset.prod_mul_distrib]
  apply Finset.prod_lt_prod_of_nonempty
  · intro p hp
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : 0 < ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i :=
      Finset.sum_pos (fun i _ => by positivity) (by simp)
    exact Nat.mul_pos h1 (by omega)
  · intro p hp
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have := geom_pred_mul (p := p) (by omega) (n.factorization p)
    rw [pow_succ] at this
    omega
  · exact Nat.nonempty_primeFactors.mpr hn

/-- Abundancy bound for a k-hyperperfect n (k > 1): (k + 1) ∏ (p - 1) < k ∏ p. -/
lemma abundancy {k n : ℕ} (hk : 1 < k) (h : IsHyperperfect k n) :
    (k + 1) * ∏ p ∈ n.primeFactors, (p - 1) < k * ∏ p ∈ n.primeFactors, p := by
  have hn := h.2.1
  have h1 := sigma_gt hk h
  have h2 := sigma_mul_prod_lt hn
  set A := ∏ p ∈ n.primeFactors, (p - 1)
  set B := ∏ p ∈ n.primeFactors, p
  set S := ∑ d ∈ n.divisors, d
  have h3 : (k + 1) * n * A ≤ k * S * A := Nat.mul_le_mul_right A h1.le
  have h4 : k * (S * A) < k * (n * B) := Nat.mul_lt_mul_of_pos_left h2 (by omega)
  have h5 : n * ((k + 1) * A) < n * (k * B) := by
    calc n * ((k + 1) * A) = (k + 1) * n * A := by ring
      _ ≤ k * S * A := h3
      _ = k * (S * A) := by ring
      _ < k * (n * B) := h4
      _ = n * (k * B) := by ring
  exact Nat.lt_of_mul_lt_mul_left h5

/-- If every element of s is at least m ≥ 1, then ∏ p * (m - 1)^|s| ≤ m^|s| * ∏ (p - 1). -/
lemma prod_ratio_le {s : Finset ℕ} {m : ℕ} (hm : 1 ≤ m) (hs : ∀ p ∈ s, m ≤ p) :
    (∏ p ∈ s, p) * (m - 1) ^ s.card ≤ m ^ s.card * ∏ p ∈ s, (p - 1) := by
  rw [← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p hp
  have := hs p hp
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, p = b + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith

/-- With m ≤ every prime factor of a k-hyperperfect n (k > 1),
(k + 1) (m - 1)^r < k m^r where r is the number of distinct prime factors. -/
lemma min_prime_ineq {k n m : ℕ} (hk : 1 < k) (h : IsHyperperfect k n) (hm : 1 ≤ m)
    (hs : ∀ p ∈ n.primeFactors, m ≤ p) :
    (k + 1) * (m - 1) ^ n.primeFactors.card < k * m ^ n.primeFactors.card := by
  have h1 := abundancy hk h
  have h2 := prod_ratio_le hm hs
  set A := ∏ p ∈ n.primeFactors, (p - 1)
  set B := ∏ p ∈ n.primeFactors, p
  set r := n.primeFactors.card
  have hA : 0 < A := Finset.prod_pos (fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega)
  have h3 : A * ((k + 1) * (m - 1) ^ r) < A * (k * m ^ r) := by
    have hpos : 0 < (m - 1) ^ r ∨ m - 1 = 0 := by
      rcases Nat.eq_zero_or_pos (m - 1) with h0 | h0
      · exact Or.inr h0
      · exact Or.inl (by positivity)
    rcases hpos with hpos | h0
    · have h4 : (k + 1) * A * (m - 1) ^ r < k * B * (m - 1) ^ r :=
        Nat.mul_lt_mul_of_pos_right h1 hpos
      have h5 : k * (B * (m - 1) ^ r) ≤ k * (m ^ r * A) := Nat.mul_le_mul_left k h2
      calc A * ((k + 1) * (m - 1) ^ r) = (k + 1) * A * (m - 1) ^ r := by ring
        _ < k * B * (m - 1) ^ r := h4
        _ = k * (B * (m - 1) ^ r) := by ring
        _ ≤ k * (m ^ r * A) := h5
        _ = A * (k * m ^ r) := by ring
    · have hm1 : m = 1 := by omega
      rw [h0, hm1]
      have hr : 0 < r := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr h.2.1)
      simp only [zero_pow hr.ne', mul_zero, one_pow, mul_one]
      exact Nat.mul_pos hA (by omega)
  exact Nat.lt_of_mul_lt_mul_left h3

/-- (k + 1) t^3 < k (t + 1)^3 forces t ≤ 3 k. -/
lemma cube_bound {k t : ℕ} (h : (k + 1) * t ^ 3 < k * (t + 1) ^ 3) : t ≤ 3 * k := by
  by_contra hc
  have ht : 3 * k + 1 ≤ t := by omega
  have h1 : (3 * k + 1) * t ≤ t * t := Nat.mul_le_mul_right t ht
  have h2 : (3 * k + 1) * (t * t) ≤ t * (t * t) := Nat.mul_le_mul_right (t * t) ht
  nlinarith

/-- (k + 1) t^2 < k (t + 1)^2 forces t ≤ 2 k. -/
lemma square_bound {k t : ℕ} (h : (k + 1) * t ^ 2 < k * (t + 1) ^ 2) : t ≤ 2 * k := by
  by_contra hc
  have ht : 2 * k + 1 ≤ t := by omega
  have h1 : (2 * k + 1) * t ≤ t * t := Nat.mul_le_mul_right t ht
  nlinarith

/-- The least prime factor of a k-hyperperfect n (k > 1) with exactly three distinct prime
factors is at most 3 k + 1. -/
lemma min_prime_le_three {k n : ℕ} (hk : 1 < k) (h : IsHyperperfect k n)
    (h3 : n.primeFactors.card = 3) :
    ∃ p ∈ n.primeFactors, p ≤ 3 * k + 1 ∧ ∀ q ∈ n.primeFactors, p ≤ q := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h.2.1
  refine ⟨n.primeFactors.min' hne, Finset.min'_mem _ _, ?_, fun q hq => Finset.min'_le _ _ hq⟩
  set m := n.primeFactors.min' hne
  have hm2 : 2 ≤ m := (Nat.prime_of_mem_primeFactors (Finset.min'_mem _ hne)).two_le
  have hi := min_prime_ineq hk h (m := m) (by omega) (fun q hq => Finset.min'_le _ _ hq)
  rw [h3] at hi
  obtain ⟨t, ht⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [ht, Nat.add_sub_cancel] at hi
  have := cube_bound hi
  omega

/-- Same with two distinct prime factors: least prime ≤ 2 k + 1. -/
lemma min_prime_le_two {k n : ℕ} (hk : 1 < k) (h : IsHyperperfect k n)
    (h2 : n.primeFactors.card = 2) :
    ∃ p ∈ n.primeFactors, p ≤ 2 * k + 1 ∧ ∀ q ∈ n.primeFactors, p ≤ q := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h.2.1
  refine ⟨n.primeFactors.min' hne, Finset.min'_mem _ _, ?_, fun q hq => Finset.min'_le _ _ hq⟩
  set m := n.primeFactors.min' hne
  have hm2 : 2 ≤ m := (Nat.prime_of_mem_primeFactors (Finset.min'_mem _ hne)).two_le
  have hi := min_prime_ineq hk h (m := m) (by omega) (fun q hq => Finset.min'_le _ _ hq)
  rw [h2] at hi
  obtain ⟨t, ht⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [ht, Nat.add_sub_cancel] at hi
  have := square_bound hi
  omega

/-- Decomposition of a number with exactly three distinct prime factors. -/
lemma three_factors {n : ℕ} (hn : n ≠ 0) (h : n.primeFactors.card = 3) :
    ∃ p q r a b c : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      0 < a ∧ 0 < b ∧ 0 < c ∧ n = p ^ a * q ^ b * r ^ c := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hs⟩ := Finset.card_eq_three.mp h
  have hp : p ∈ n.primeFactors := by rw [hs]; simp
  have hq : q ∈ n.primeFactors := by rw [hs]; simp
  have hr : r ∈ n.primeFactors := by rw [hs]; simp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hq' := Nat.prime_of_mem_primeFactors hq
  have hr' := Nat.prime_of_mem_primeFactors hr
  refine ⟨p, q, r, n.factorization p, n.factorization q, n.factorization r, hp', hq', hr',
    hpq, hpr, hqr,
    hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp),
    hq'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hq),
    hr'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hr), ?_⟩
  have := n_prod hn
  rw [hs, Finset.prod_insert (by simp [hpq, hpr]), Finset.prod_pair hqr, ← mul_assoc] at this
  exact this

/-- σ(p^a q^b r^c) = σ(p^a) σ(q^b) σ(r^c) for distinct primes. -/
lemma sigma_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (a b c : ℕ) :
    ∑ d ∈ (p ^ a * q ^ b * r ^ c).divisors, d =
      (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) *
        (∑ l ∈ Finset.range (c + 1), r ^ l) := by
  have hc1 : Nat.Coprime (p ^ a * q ^ b) (r ^ c) :=
    Nat.Coprime.mul_left (Nat.coprime_pow_primes a c hp hr hpr) (Nat.coprime_pow_primes b c hq hr hqr)
  rw [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hc1,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.coprime_pow_primes a b hp hq hpq),
    sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hq, sigma_one_apply_prime_pow hr]

/-- The hyperperfect equation for p^a q^b r^c: n + k (n + 1) = 1 + k σ(p^a) σ(q^b) σ(r^c). -/
lemma master_three {k p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h : IsHyperperfect k (p ^ a * q ^ b * r ^ c)) :
    p ^ a * q ^ b * r ^ c + k * (p ^ a * q ^ b * r ^ c + 1) =
      1 + k * ((∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) *
        (∑ l ∈ Finset.range (c + 1), r ^ l)) := by
  rw [← sigma_three hp hq hr hpq hpr hqr a b c]
  exact general_eq h

/-- Bernoulli-type bound: (t + 1)^r (t - r) ≤ t^(r+1) over ℤ for t ≥ 0. -/
lemma bern_aux (t : ℤ) (ht : 0 ≤ t) (r : ℕ) : (t + 1) ^ r * (t - r) ≤ t ^ (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h0 : (0 : ℤ) ≤ (t + 1) ^ r := by positivity
    have h1 : t * ((t + 1) ^ r * (t - r)) ≤ t * t ^ (r + 1) := mul_le_mul_of_nonneg_left ih ht
    push_cast
    have e1 : (t + 1) ^ (r + 1) * (t - (r + 1)) =
        t * ((t + 1) ^ r * (t - r)) - (r + 1) * (t + 1) ^ r := by ring
    have e2 : t ^ (r + 1 + 1) = t * t ^ (r + 1) := by ring
    rw [e1, e2]
    have h2 : (0 : ℤ) ≤ (r + 1) * (t + 1) ^ r := by positivity
    linarith

/-- (k + 1) t^r < k (t + 1)^r forces t < r (k + 1). -/
lemma gen_bound {k t r : ℕ} (h : (k + 1) * t ^ r < k * (t + 1) ^ r) : t < r * (k + 1) := by
  by_contra hc
  have ht : r * (k + 1) ≤ t := by omega
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp at h
  have hz : ((k : ℤ) + 1) * (t : ℤ) ^ r < k * ((t : ℤ) + 1) ^ r := by exact_mod_cast h
  have htz : (r : ℤ) * (k + 1) ≤ t := by exact_mod_cast ht
  have hrz : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hb := bern_aux (t : ℤ) (by positivity) r
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp at h
    · exact h0
  have hk1z : (1 : ℤ) ≤ k := by exact_mod_cast hk1
  have hrk : (1 : ℤ) ≤ r * k := one_le_mul_of_one_le_of_one_le hrz hk1z
  have hpos : (0 : ℤ) < (t : ℤ) - r := by linarith
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have h1 : (k : ℤ) * ((t + 1) ^ r * (t - r)) ≤ k * t ^ (r + 1) :=
    mul_le_mul_of_nonneg_left hb hk0
  have h2 : (k : ℤ) * t ≤ (k + 1) * (t - r) := by nlinarith
  have htr : (0 : ℤ) ≤ (t : ℤ) ^ r := by positivity
  have h3 : (k : ℤ) * t ^ (r + 1) ≤ (k + 1) * (t - r) * t ^ r := by
    have := mul_le_mul_of_nonneg_right h2 htr
    calc (k : ℤ) * t ^ (r + 1) = k * t * t ^ r := by ring
      _ ≤ _ := this
  have h4 : (k : ℤ) * (t + 1) ^ r * (t - r) ≤ (k + 1) * t ^ r * (t - r) := by
    calc (k : ℤ) * (t + 1) ^ r * (t - r) = k * ((t + 1) ^ r * (t - r)) := by ring
      _ ≤ k * t ^ (r + 1) := h1
      _ ≤ (k + 1) * (t - r) * t ^ r := h3
      _ = (k + 1) * t ^ r * (t - r) := by ring
  have h5 := le_of_mul_le_mul_right h4 hpos
  linarith

/-- For odd k > 1, a k-hyperperfect n has a prime factor below (number of distinct prime
factors) * (k + 1). -/
lemma min_prime_lt_card {k n : ℕ} (hk_odd : Odd k) (hk : 1 < k) (h : IsHyperperfect k n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p < n.primeFactors.card * (k + 1) := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h.2.1
  have hmem := Finset.min'_mem _ hne
  set m := n.primeFactors.min' hne
  have hmp := Nat.prime_of_mem_primeFactors hmem
  refine ⟨m, hmp, Nat.dvd_of_mem_primeFactors hmem, ?_⟩
  have hm2 : 2 ≤ m := hmp.two_le
  have hi := min_prime_ineq hk h (m := m) (by omega) (fun q hq => Finset.min'_le _ _ hq)
  obtain ⟨t, ht⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [ht, Nat.add_sub_cancel] at hi
  have hb := gen_bound hi
  have hle : m ≤ n.primeFactors.card * (k + 1) := by omega
  rcases Nat.lt_or_ge m (n.primeFactors.card * (k + 1)) with hlt | hge
  · exact hlt
  · exfalso
    have heq : m = n.primeFactors.card * (k + 1) := by omega
    obtain ⟨c, hc⟩ := hk_odd
    have hev : Even m := ⟨n.primeFactors.card * (c + 1), by rw [heq, hc]; ring⟩
    have h2 : m = 2 := (Nat.Prime.even_iff hmp).mp hev
    have hcard : 0 < n.primeFactors.card := Finset.card_pos.mpr hne
    have : 1 * (k + 1) ≤ n.primeFactors.card * (k + 1) := Nat.mul_le_mul_right _ hcard
    omega

/-- For odd k > 1, a k-hyperperfect n with exactly three distinct prime factors has a prime
factor below 3 k. -/
lemma min_prime_lt_three_k {k n : ℕ} (hk_odd : Odd k) (hk : 1 < k) (h : IsHyperperfect k n)
    (h3 : n.primeFactors.card = 3) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p < 3 * k := by
  obtain ⟨p, hp, hle, -⟩ := min_prime_le_three hk h h3
  have hpp := Nat.prime_of_mem_primeFactors hp
  refine ⟨p, hpp, Nat.dvd_of_mem_primeFactors hp, ?_⟩
  obtain ⟨c, hc⟩ := hk_odd
  rcases (show p < 3 * k ∨ p = 3 * k ∨ p = 3 * k + 1 by omega) with h1 | h1 | h1
  · exact h1
  · exfalso
    have h3d : 3 ∣ p := ⟨k, h1⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp h3d
    omega
  · exfalso
    have hev : Even p := ⟨3 * c + 2, by omega⟩
    have := (Nat.Prime.even_iff hpp).mp hev
    omega

/-- Second-prime abundancy bound: for a prime factor p of a k-hyperperfect n (k > 1) and any
m ≥ 1 below all the other prime factors, with c = r - 1 the number of other prime factors,
(k + 1) (p - 1) (m - 1)^c < k p m^c. -/
lemma second_prime_ineq {k n p m : ℕ} (hk : 1 < k) (h : IsHyperperfect k n)
    (hp : p ∈ n.primeFactors) (hm : 1 ≤ m) (hs : ∀ q ∈ n.primeFactors.erase p, m ≤ q) :
    (k + 1) * (p - 1) * (m - 1) ^ (n.primeFactors.card - 1) <
      k * p * m ^ (n.primeFactors.card - 1) := by
  have h1 := abundancy hk h
  rw [← Finset.mul_prod_erase _ _ hp, ← Finset.mul_prod_erase _ (fun q => q) hp] at h1
  have h2 := prod_ratio_le hm hs
  rw [Finset.card_erase_of_mem hp] at h2
  set A := ∏ q ∈ n.primeFactors.erase p, (q - 1)
  set B := ∏ q ∈ n.primeFactors.erase p, q
  set c := n.primeFactors.card - 1
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hA : 0 < A := Finset.prod_pos (fun q hq => by
    have := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)).two_le
    omega)
  rcases Nat.eq_zero_or_pos ((m - 1) ^ c) with h0 | hpos
  · rw [h0, mul_zero]
    have : 0 < m ^ c := by positivity
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) this
  · have h4 : (k + 1) * ((p - 1) * A) * (m - 1) ^ c < k * (p * B) * (m - 1) ^ c :=
      Nat.mul_lt_mul_of_pos_right h1 hpos
    have h5 : k * p * (B * (m - 1) ^ c) ≤ k * p * (m ^ c * A) := Nat.mul_le_mul_left _ h2
    have h3 : A * ((k + 1) * (p - 1) * (m - 1) ^ c) < A * (k * p * m ^ c) := by
      calc A * ((k + 1) * (p - 1) * (m - 1) ^ c) = (k + 1) * ((p - 1) * A) * (m - 1) ^ c := by
            ring
        _ < k * (p * B) * (m - 1) ^ c := h4
        _ = k * p * (B * (m - 1) ^ c) := by ring
        _ ≤ k * p * (m ^ c * A) := h5
        _ = A * (k * p * m ^ c) := by ring
    exact Nat.lt_of_mul_lt_mul_left h3

/-- Arithmetic step: (k + 1)(p - 1) t^2 < k p (t + 1)^2 with t ≥ 1 gives (p - k - 1) t < 3 k p. -/
lemma second_arith {k p t : ℕ} (hp : 1 ≤ p) (ht : 1 ≤ t)
    (h : (k + 1) * (p - 1) * t ^ 2 < k * p * (t + 1) ^ 2) : (p - k - 1) * t < 3 * k * p := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  rcases Nat.lt_or_ge (s + 1) (k + 1) with hlt | hge
  · have : s + 1 - k - 1 = 0 := by omega
    rw [this, zero_mul]
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        simp at h
      · exact h0
    positivity
  · obtain ⟨d, hd⟩ : ∃ d, s = k + d := ⟨s - k, by omega⟩
    subst hd
    have e : k + d + 1 - k - 1 = d := by omega
    rw [e]
    have h1 : d * t ^ 2 < k * (k + d + 1) * (2 * t + 1) := by nlinarith
    have h2 : k * (k + d + 1) * (2 * t + 1) ≤ 3 * k * (k + d + 1) * t := by
      have h0 : 2 * t + 1 ≤ 3 * t := by omega
      calc k * (k + d + 1) * (2 * t + 1) ≤ k * (k + d + 1) * (3 * t) :=
            Nat.mul_le_mul_left _ h0
        _ = 3 * k * (k + d + 1) * t := by ring
    have h3 : d * t * t < 3 * k * (k + d + 1) * t := by
      calc d * t * t = d * t ^ 2 := by ring
        _ < _ := lt_of_lt_of_le h1 h2
    exact Nat.lt_of_mul_lt_mul_right h3

/-- Three prime factors: with p the least and q the second least prime factor of a
k-hyperperfect n (odd k > 1), p < 3 k and (p - k - 1)(q - 1) < 3 k p. Since p > k and both are
odd, p - k - 1 ≥ 1, so q < 3 k p + 1: for each k only finitely many (p, q) are possible. -/
lemma two_least_three {k n : ℕ} (hk_odd : Odd k) (hk : 1 < k) (h : IsHyperperfect k n)
    (h3 : n.primeFactors.card = 3) :
    ∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p < q ∧
      (∀ r ∈ n.primeFactors, p ≤ r) ∧ (∀ r ∈ n.primeFactors, r ≠ p → q ≤ r) ∧
      p < 3 * k ∧ (p - k - 1) * (q - 1) < 3 * k * p := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h.2.1
  have hpm := Finset.min'_mem _ hne
  set p := n.primeFactors.min' hne
  have hcard : (n.primeFactors.erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hpm, h3]
  have hne2 : (n.primeFactors.erase p).Nonempty := by
    rw [← Finset.card_pos, hcard]
    norm_num
  have hqm := Finset.min'_mem _ hne2
  set q := (n.primeFactors.erase p).min' hne2
  have hqp : q ≠ p := Finset.ne_of_mem_erase hqm
  have hqmem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hqm
  have hpq : p ≤ q := Finset.min'_le _ _ hqmem
  have hp2 := (Nat.prime_of_mem_primeFactors hpm).two_le
  have hq2 := (Nat.prime_of_mem_primeFactors hqmem).two_le
  have hsec : ∀ r ∈ n.primeFactors, r ≠ p → q ≤ r := fun r hr hrp =>
    Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hrp, hr⟩)
  have hi := second_prime_ineq hk h hpm (m := q) (by omega)
    (fun r hr => Finset.min'_le _ _ hr)
  rw [h3] at hi
  obtain ⟨t, ht⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
  have hi' : (k + 1) * (p - 1) * t ^ 2 < k * p * (t + 1) ^ 2 := by
    rw [ht, Nat.add_sub_cancel] at hi
    exact hi
  have hb := second_arith (by omega) (by omega) hi'
  obtain ⟨p', hp', hdvd, hlt⟩ := min_prime_lt_three_k hk_odd hk h h3
  have hpp' : p ≤ p' := Finset.min'_le _ _ (Nat.mem_primeFactors.mpr ⟨hp', hdvd, by
    have := h.2.1
    omega⟩)
  refine ⟨p, q, hpm, hqmem, lt_of_le_of_ne hpq (Ne.symm hqp),
    fun r hr => Finset.min'_le _ _ hr, hsec, by omega, ?_⟩
  rw [ht, Nat.add_sub_cancel]
  exact hb

end Lib

theorem main : H1 → H2 → type_of% @HyperperfectNumber.mccranie_odd_hyperperfect_conjecture := by
  intro h1 h2 k n hk_odd hk hn
  have hc1 : n.primeFactors.card ≠ 3 := by
    intro h3
    exact h1 k n hk_odd hk hn (all_factors_gt hn) (sigma_mod4_general hk_odd hk hn)
      (euler_form hk_odd hk hn) (Lib.two_least_three hk_odd hk hn h3) h3
  have hc2 := h2 k n hk_odd hk hn (all_factors_gt hn) (sigma_mod4_general hk_odd hk hn)
    (euler_form hk_odd hk hn) (small_factor hk hn)
  have hn1 : 1 < n := hn.2.1
  have hn0 : n ≠ 0 := by omega
  rcases (show n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 by
    omega) with h0 | h1c | h2c
  · rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h0
    omega
  · obtain ⟨p, a, hp, ha, hpa⟩ :=
      (isPrimePow_nat_iff n).mp (isPrimePow_iff_card_primeFactors_eq_one.mpr h1c)
    subst hpa
    exact (not_prime_pow hp ha hn).elim
  · obtain ⟨p, q, a, b, hp, hq, hpq, ha, hb, rfl⟩ := two_factors hn0 h2c
    have hn' : IsHyperperfect k (q ^ b * p ^ a) := by rwa [mul_comm] at hn
    have ha3 := exp_le_three hk_odd hk hp hq hpq ha hb hn
    have hb3 := exp_le_three hk_odd hk hq hp hpq.symm hb ha hn'
    rcases shape hk_odd hk hp hq hpq ha hb hn with ⟨hae, -, -, hb4⟩ | ⟨-, hbe, -, ha4⟩
    · have hb1 : b = 1 := by omega
      have ha2 : a = 2 := by
        obtain ⟨c, hc⟩ := hae
        omega
      subst hb1 ha2
      obtain ⟨h4, h5⟩ := p2q_classify hk_odd hk hp hq hpq hn
      have e1 : (3 * k + 1) / 2 = p := by omega
      rw [e1, ← h5]
      exact ⟨hp, hq, by ring⟩
    · have ha1 : a = 1 := by omega
      have hb2 : b = 2 := by
        obtain ⟨c, hc⟩ := hbe
        omega
      subst ha1 hb2
      obtain ⟨h4, h5⟩ := p2q_classify hk_odd hk hq hp hpq.symm hn'
      have e1 : (3 * k + 1) / 2 = q := by omega
      rw [e1, ← h5]
      exact ⟨hq, hp, by ring⟩

end OMA.R_HyperperfectNumber_mccranie_odd_hyperperfect_conjecture_R2
