import OMAReductions.R_PerfectNumbers_odd_perfect_number_lower_bound_R1
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.FactorisationProperties

/-!
Ochem and Rao, Mathematics of Computation 81 (2012), Theorem 1, split the
size bound into a factor-chain search and an estimate of abundancy. Their
forbidden primes, in search order, are 127, 19, 7, 11, 331, 31, 97, 61, 13,
398581, 1093, 3, 5, 307, 17. Their product is 5001473436652898064596041305.

H1 asks for the finite search excluding those primes. H2 is the endgame for
arbitrary odd candidates: when neither the number nor its divisor sum has
a forbidden prime factor, and the divisor sum is not a multiple of four,
the candidate must be deficient within the stated size range.
-/

open Nat ArithmeticFunction

namespace OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1

def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 5001473436652898064596041305

def H2 : Prop :=
  ∀ n : ℕ, Odd n → n ≤ 10 ^ 1500 → n.Coprime 5001473436652898064596041305 →
    (sigma 1 n).Coprime 5001473436652898064596041305 → ¬ 4 ∣ sigma 1 n → sigma 1 n < 2 * n

lemma exact_component {n p : ℕ} (hn : n.Perfect) (hp : p.Prime) :
    sigma 1 (p ^ n.factorization p) ∣ 2 * n := by
  have hsum : sigma 1 n = 2 * n := by
    rw [sigma_one_apply, (perfect_iff_sum_divisors_eq_two_mul hn.2).mp hn]
  have hc := (coprime_ordCompl hp hn.2.ne').pow_left (n.factorization p)
  have hmul := isMultiplicative_sigma (k := 1) |>.map_mul_of_coprime hc
  rw [ordProj_mul_ordCompl_eq_self n p] at hmul
  rw [← hsum, hmul]
  exact Nat.dvd_mul_right _ _

lemma geometric_block {p b k : ℕ} :
    (∑ i ∈ Finset.range b, p ^ i) ∣ ∑ i ∈ Finset.range (b * k), p ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add]
    apply dvd_add ih
    simp_rw [pow_add]
    rw [← Finset.mul_sum]
    exact dvd_mul_left _ _

lemma compressed_component {n p d : ℕ} (hn : n.Perfect) (hp : p.Prime)
    (hd : d ∣ n.factorization p + 1) : (∑ i ∈ Finset.range d, p ^ i) ∣ 2 * n := by
  obtain ⟨k, hk⟩ := hd
  have h := exact_component hn hp
  rw [sigma_one_apply_prime_pow hp, hk] at h
  exact geometric_block.trans h

lemma forced_prime {n p d q : ℕ} (hn : n.Perfect) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hd : d ∣ n.factorization p + 1)
    (hf : q ∣ ∑ i ∈ Finset.range d, p ^ i) : q ∣ n :=
  (hq.dvd_mul.mp (hf.trans (compressed_component hn hp hd))).resolve_left
    (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h))

lemma abundant_leaf {n c : ℕ} (hn : n.Perfect) (hc : c ∣ n) (ha : c.Abundant) : False :=
  (perfect_iff_not_abundant_and_not_deficient hn.2.ne'.symm).mp hn |>.1 (ha.of_dvd hc hn.2.ne')

lemma exponent_23_of_seven_excluded {n : ℕ} (ho : Odd n) (hn : n.Perfect)
    (h23 : 23 ∣ n) (h7 : ¬ 7 ∣ n) : 4 ≤ n.factorization 23 := by
  have hp : Nat.Prime 23 := by decide
  have he := hp.factorization_pos_of_dvd hn.2.ne' h23
  have evenBlock : ¬ 2 ∣ n.factorization 23 + 1 := by
    intro hd
    have h := compressed_component hn hp hd
    have hf : 4 ∣ ∑ i ∈ Finset.range 2, 23 ^ i := by decide
    have h4 := hf.trans h
    obtain ⟨k, hk⟩ := ho
    omega
  have tripleBlock : ¬ 3 ∣ n.factorization 23 + 1 := by
    intro hd
    exact h7 (forced_prime hn hp (by decide : Nat.Prime 7) (by decide) hd (by decide))
  omega

theorem main : H1 → H2 → OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1.H1 := by
  intro search endgame n ho hn
  by_contra! hsmall
  have hc := search n ho hn hsmall
  have hsum : sigma 1 n = 2 * n := by
    rw [sigma_one_apply, (perfect_iff_sum_divisors_eq_two_mul hn.2).mp hn]
  have htwo : Nat.Coprime 2 5001473436652898064596041305 := by decide
  have h4 : ¬ 4 ∣ sigma 1 n := by
    rw [hsum]
    obtain ⟨k, hk⟩ := ho
    omega
  have h := endgame n ho hsmall hc (hsum ▸ htwo.mul_left hc) h4
  omega

end OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1
