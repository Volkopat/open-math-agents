import FormalConjectures.Wikipedia.HyperperfectNumber
import Mathlib

-- Credit: @rickmanelius

namespace OMA.R_HyperperfectNumber_mccranie_odd_hyperperfect_conjecture_R1

open HyperperfectNumber ArithmeticFunction

/-- No k-hyperperfect number n with k odd and k > 1 has exactly three distinct prime factors.
The side conditions are proved by main for every such n: its prime factors all exceed k, its
divisor sum is 2 mod 4, and it has Euler form (exactly one prime q has odd exponent, and q and
that exponent are both 1 mod 4). -/
def H1 : Prop :=
  ∀ k n : ℕ, Odd k → 1 < k → IsHyperperfect k n → (∀ p : ℕ, p.Prime → p ∣ n → k < p) →
    (∑ d ∈ n.divisors, d) % 4 = 2 →
    (∃ q : ℕ, q.Prime ∧ q % 4 = 1 ∧ n.factorization q % 4 = 1 ∧
      ∀ p : ℕ, p ≠ q → Even (n.factorization p)) →
    n.primeFactors.card ≠ 3

/-- No k-hyperperfect number n with k odd and k > 1 has four or more distinct prime factors
(same side conditions as H1). -/
def H2 : Prop :=
  ∀ k n : ℕ, Odd k → 1 < k → IsHyperperfect k n → (∀ p : ℕ, p.Prime → p ∣ n → k < p) →
    (∑ d ∈ n.divisors, d) % 4 = 2 →
    (∃ q : ℕ, q.Prime ∧ q % 4 = 1 ∧ n.factorization q % 4 = 1 ∧
      ∀ p : ℕ, p ≠ q → Even (n.factorization p)) →
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

theorem main : H1 → H2 → type_of% @HyperperfectNumber.mccranie_odd_hyperperfect_conjecture := by
  intro h1 h2 k n hk_odd hk hn
  have hc1 := h1 k n hk_odd hk hn (all_factors_gt hn) (sigma_mod4_general hk_odd hk hn)
    (euler_form hk_odd hk hn)
  have hc2 := h2 k n hk_odd hk hn (all_factors_gt hn) (sigma_mod4_general hk_odd hk hn)
    (euler_form hk_odd hk hn)
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

end OMA.R_HyperperfectNumber_mccranie_odd_hyperperfect_conjecture_R1
