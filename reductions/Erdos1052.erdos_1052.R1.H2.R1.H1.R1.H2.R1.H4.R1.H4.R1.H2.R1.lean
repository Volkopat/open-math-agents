import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1
import Mathlib

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H2.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H2
-- Credit: @aroth01

/-!
# 32 | e: every z >= 823 and 119 more primes are settled; for z >= 23 only a = 2 mod 4 is left

A reduction of step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1 (the unitary perfect number n has
exactly one repeated odd prime z, 7 <= z < 2100, exponent e = v_z(n) divisible by 32; bound a = v2(n)).
It splits by the size of z and by a mod 4, and does not use the value of e beyond 8 | e; the three open
statements H1, H2, H3 keep the hypothesis 32 | e.
Five parts of the step are PROVED BELOW with no hypothesis:
  (A) z >= 61 and a odd: a <= 7;
  (B) z >= 61 and 4 | a: no solution, except z = 257 with a = 8 mod 16;
  (C) a = 2 mod 4: a <= 21 for every z >= 823, for 113 of the 125 primes 61 <= z < 823, and for z = 29, 43,
      47, 59;
  (D) z = 7 and z = 31: a <= 21;
  (E) z in {23, 29, 37, 41, 43, 47, 53, 59}: a odd gives a <= 7, and 4 | a has no solution.
So every z >= 823, these 113 primes, 7, 29, 31, 43, 47 and 59 are settled (a <= 21); for the other 12 primes
z >= 61 and for z = 23, 37, 41, 53 only a = 2 mod 4 is left.

Notation of the parent: P is the set of simple odd primes and
  (E)  (2^a + 1)(1 + z^e) prod_P (p + 1) = 2^(a+1) z^e prod_P p.
Each odd prime other than z divides one factor of the left side at most (its source), and once.
All three parts use `master_gen` (core prime z, kept child = least odd prime factor other than z); the leaves
are the Mersenne primes (`mersenne_bound`) and the primes x with x + 1 = 2^i z^j, j >= 1, which weigh at most
z^2/(z^2-3) * z/(z-2) (`zleaves_generic`). What differs is the weight of 3.

(A) a odd (`odd_master`, `odd_bound61`). 3 | 2^a + 1 is the source of 3, so 3 has no consumer and weighs 4/3
instead of 2. Default weights elsewhere: for z >= 61 and a >= 9 the total is at most
  (1+2^-9)(1+1/61^2)(4/3)(4/3)(16/15)(64/63)(2048/2047)(3721/3718)(61/59) = 1.99872 < 2.

(B) 4 | a (`exists_fermat_prime`, `two_pow_succ_dvd_pred`, `v2_large`, `pinned_master`, `pinned_generic`,
`four_dvd_dead61`). Let a = 2^k t, t odd. The Fermat number 2^(2^k) + 1 divides 2^a + 1 and is 2 mod 3, so a
prime c = 2 mod 3 divides it, and 2^(k+1) divides c - 1. The step excludes k = 2 and k = 4, ..., 10, and k = 3
unless z is 11, 43 or 257; so k >= 11 and c >= 4097 > z, or z = 257 and a = 8 mod 16. In the first case c is
a simple prime with 3 | c + 1, the only one, so 3 weighs (4/3)(4098/4096); total at most 1.99677 < 2.

(C) a = 2 mod 4 (`setup5`, `lower_kill`, `table_master`, `amod4_large`, `amod4_skip`, `zleaves_one`, `amod4_leaf`,
`table_master_q`, `amod4_leafq`, `amod4_dead_mid`). Now 5 | 2^a + 1 is a simple prime
without consumer and the only simple prime p with 3 | p + 1, so 3 weighs 8/5 and the other simple primes
must multiply to just below 5/4. Case split on which of 13, 31, 103, 127 are simple primes:
  too much: 3, 5, 7, 13, 31 give 2.0328 > 2 and 3, 5, 7, 13, 103, 127 give 2.0040 > 2 (`lower_kill`);
  too little (`table_master`, a >= 22, z >= 823): 7 <- 13 <- 103 with 31, 127 not simple: 1.99903;
  7 <- 13 with 103, 31 not simple: 1.99605; 13 not simple: 1.99449.
For z < 823 the same three cases work when the leaves are bounded better (`zleaves_skip`): if 2^k z - 1 is not
prime for k = 1, ..., s, the leaves weigh at most z^2/(z^2-3) * u/(u-2) with u = 2^s z. This brings the worst total
(the first case) below 2 for 90 primes z, with s = 0 (691 <= z), s = 1 (347 <= z <= 683), s = 2, 3 or 4.
For 14 more primes (89, 163, 197, 263, 281, 293, 379, 499, 547, 577, 601, 607, 619, 661) exactly one
q0 = 2^k z - 1 with k <= s is prime, and the leaves weigh at most z^2/(z^2-3) * (q0+1)/(q0-1) * u/(u-2)
(`zleaves_one`, `amod4_leaf`); for example z = 89: q0 = 1423, s = 5, total 1.99913. The same lemma settles
z = 43 (q0 = 5503 = 2^7 * 43 - 1, total 1.99888) and z = 59 (q0 = 241663 = 2^12 * 59 - 1, total 1.99592).
For 8 more primes (103, 131, 211, 227, 271, 307, 337, 367) the leaf q0 gets its own weight (`kept_parent_form`,
`table_master_q`, `far_of_small`, `zleaves_except`, `amod4_leafq`): a kept parent p of q0 has
p + 1 = q0 * 2^i * z^j or p + 1 >= 2 q0 (q0 + 1), and no q0 * 2^i - 1 with i < i0 is prime, so p >= Nq with
Nq + 1 = min(q0 * 2^i0, 60 q0), and q0 weighs (1 + 1/q0)(Nq+1)/(Nq-1) instead of (q0+1)/(q0-1). For example
z = 307: q0 = 613, Nq = 4903, total 1.99992; z = 211: q0 = 421, Nq = 25259, total 1.99978.
For z = 47 (q0 = 751, Nq = 6007) and z = 29 (q0 = 463, Nq = 14815) the leaves 2^k z^2 - 1 are bounded better as
well (`zleaves_except2`: none is prime for k <= 4, so they weigh at most u2/(u2-2), u2 = 16 z^2, and the leaves
with z^3 | x + 1 at most z^3/(z^3-3)): totals 1.99768 and 1.99937.
For z = 439 two leaves are exceptional, 877 = 2 * 439 - 1 and 3511 = 8 * 439 - 1 (`zleaves_two`, s = 12): total
1.99989.
The list of the 113 settled primes is in H2; `amod4_dead_mid` has the same list with 29, 43, 47, 59 in front.

(D) z = 7 and z = 31 (`small_dead`). These primes are not simple, so the weight of 7 (or 31) drops out.
a odd (`odd_master_b`, `odd_seven`, `odd_thirtyone`): totals 1.92472 for z = 7, a >= 5 and 1.95471 for z = 31,
a >= 7. 4 | a (`four_dvd_small`, `pinned_seven`, `pinned_thirtyone`): totals 1.86822 and 1.94146.
a = 2 mod 4 (`amod4_7`, `amod4_31`): totals at most 1.99950; the leaves 13 (for z = 7) and 991 (for z = 31) have
their own weights, and for z = 31 the primes 3, 5, 7, 13, 61 together are too much.

(E) z in {23, 29, 37, 41, 43, 47, 53, 59} (`odd_leaf`, `pinned_leaf`, `small_core`, `small8_dead`). The same
weights as in (A) and (B) with the sharper leaf bounds of `zleaves_skip` (23, 29: no prime 2z - 1, 4z - 1;
41, 43, 47, 53, 59: 2z - 1 not prime) and `zleaves_one` (37: only 73 = 2 * 37 - 1 up to 16 * 37 - 1).
Totals at most 1.99731 (a odd, a >= 9) and 1.99536 (4 | a).
For z = 43 the step allows a = 8 mod 16; then the Fermat prime is 257, a simple prime with 3 | 258, so 3
weighs (4/3)(258/256) (`pinned_master257`, `z43_dead`), and the leaves 2^k 43 - 1 start at k = 7: total 1.95563.

H1 (OPEN): z in {11, 13, 17, 19}; every condition of the step kept.
H2 (OPEN): a = 2 mod 4 and z one of 23, 37, 41, 53 or one of the 12 primes 61 <= z < 823 not
  settled in (C): 61, 71, 79, 83, 97, 137, 139, 157, 173, 199, 229, 331
  (stated as: z not in the list of the 113 settled primes; a mod 20 and a mod 28 kept).
H3 (OPEN): z = 257 and a = 8 mod 16 (then the Fermat prime is 257 = z itself, so 3 is not pinned).
For H2: with one special leaf the worst total of these 16 primes is between 2.0009 (z = 199) and 2.034 (z = 79),
so more case splits on small simple primes are needed, as was done for the leaves 13, 103, 991 in the proof of
the sibling step H1 (e odd). An exact search closes 10 of the 12 primes z >= 61 (all but z = 83 and z = 97).

The lemmas `facts`, `master_gen`, `mersenne_bound`, `zleaf_bound`, `fiber_bound`, `kernel_balance_one`,
`simple_of_unique_repeated`, `three_dvd_two_pow_add_one` and the other imported lemmas are from the parent
reductions by @adammcarter.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts three_dvd_two_pow_add_one kernel_balance_one
  master_gen mersenne_bound zleaf_bound fiber_bound two_pow_of_no_odd_prime
  two_pow_mul_pow_of_odd_primes_eq one_add_le_B B_anti B_nonneg)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)

-- H1: a is bounded when z is one of 11, 13, 17, 19; all conditions kept.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    z ∈ ({11, 13, 17, 19} : Finset ℕ) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when a = 2 mod 4 and z is one of 23, 37, 41, 53 or one of the 12 primes with
-- 61 <= z < 823 that are not in the list below: 61, 71, 79, 83, 97, 137, 139, 157, 173, 199, 229, 331.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (z ∈ ({23, 37, 41, 53} : Finset ℕ) ∨ (61 ≤ z ∧ z < 823 ∧
      z ∉ ({67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181, 191, 193, 197,
      211, 223, 227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
      317, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
      439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
      563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
      661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
      797, 809, 811, 821} : Finset ℕ))) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H3: a is bounded when z = 257 and a = 8 mod 16.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    n.factorization 257 % 32 = 0 →
    padicValNat 2 n % 16 = 8 →
    padicValNat 2 n ≤ A

/-- A product of numbers that are `1` mod `3` is `1` mod `3`. -/
theorem o25_list_prod_mod_three_eq_one : ∀ l : List ℕ, (∀ p ∈ l, p % 3 = 1) → l.prod % 3 = 1
  | [], _ => by simp
  | p :: l, h => by
    have hp := h p (by simp)
    have hl := o25_list_prod_mod_three_eq_one l (fun q hq => h q (by simp [hq]))
    rw [List.prod_cons, Nat.mul_mod, hp, hl]

/-- A number that is `2` mod `3` has a prime factor that is `2` mod `3`. -/
theorem o25_exists_prime_two_mod_three {n : ℕ} (hn : n % 3 = 2) :
    ∃ r, r.Prime ∧ r ∣ n ∧ r % 3 = 2 := by
  by_contra hcon
  push Not at hcon
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have key := o25_list_prod_mod_three_eq_one n.primeFactorsList (fun p hp => by
    have hpp := Nat.prime_of_mem_primeFactorsList hp
    have hd := Nat.dvd_of_mem_primeFactorsList hp
    have h2 := hcon p hpp hd
    have h0 : p % 3 ≠ 0 := by
      intro h0
      have : 3 ∣ n := (Nat.dvd_of_mod_eq_zero h0).trans hd
      omega
    omega)
  rw [Nat.prod_primeFactorsList hn0] at key
  omega

/-- For `m` even and positive, some prime `c = 2 (mod 3)` divides `2 ^ m + 1`: a prime factor of the Fermat
number `2 ^ 2 ^ k + 1`, where `2 ^ k` is the exact power of `2` in `m` (`m = 2 ^ k * t`, `t` odd). -/
theorem exists_fermat_prime {m : ℕ} (hm0 : m ≠ 0) (hme : Even m) :
    ∃ c k t : ℕ, c.Prime ∧ c ≠ 2 ∧ c % 3 = 2 ∧ c ∣ 2 ^ m + 1 ∧ 1 ≤ k ∧ c ∣ 2 ^ 2 ^ k + 1 ∧
      Odd t ∧ m = 2 ^ k * t := by
  obtain ⟨k, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have hk : 1 ≤ k := by
    by_contra hk0
    obtain rfl : k = 0 := by omega
    rw [pow_zero, one_mul] at hme
    exact (Nat.not_even_iff_odd.mpr ht) hme
  have hF : 2 ^ 2 ^ k + 1 ∣ 2 ^ (2 ^ k * t) + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ 2 ^ k) 1 ht
    rwa [one_pow, ← pow_mul] at h
  have hF3 : (2 ^ 2 ^ k + 1) % 3 = 2 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : (2 : ℕ) ^ 2 ^ (j + 1) % 3 = 1 := by
      rw [pow_succ', pow_mul, Nat.pow_mod]
      norm_num
    omega
  obtain ⟨c, hc, hcF, hc3⟩ := o25_exists_prime_two_mod_three hF3
  have hc2 : c ≠ 2 := by
    rintro rfl
    exact absurd ((Nat.dvd_add_right (dvd_pow_self 2 (by positivity))).mp hcF) (by norm_num)
  exact ⟨c, k, t, hc, hc2, hc3, hcF.trans hF, hk, hcF, ht, rfl⟩

/-- A prime factor of the Fermat number `2 ^ 2 ^ k + 1` is `1` modulo `2 ^ (k + 1)`. -/
theorem two_pow_succ_dvd_pred {z k : ℕ} (hz : z.Prime) (h : z ∣ 2 ^ 2 ^ k + 1) :
    2 ^ (k + 1) ∣ z - 1 := by
  have := Fact.mk hz
  have hz2 : z ≠ 2 := by
    rintro rfl
    exact absurd ((Nat.dvd_add_right (dvd_pow_self 2 (by positivity))).mp h) (by norm_num)
  have h1 : (2 : ZMod z) ^ 2 ^ k = -1 := by
    have h0 := (ZMod.natCast_eq_zero_iff (2 ^ 2 ^ k + 1) z).mpr h
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hne0 : (2 : ZMod z) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod z) = 0 := by exact_mod_cast h0
    exact hz2 ((Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 z).mp h0'))
  have hnot : ¬ (2 : ZMod z) ^ 2 ^ k = 1 := by
    rw [h1]
    intro h11
    apply hne0
    linear_combination (-1 : ZMod z) * h11
  have hfin : (2 : ZMod z) ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ, pow_mul, h1]
    norm_num
  have hord : orderOf (2 : ZMod z) = 2 ^ (k + 1) := orderOf_eq_prime_pow hnot hfin
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hne0

/-- `2 ^ r * (2 s + 1)` is `2 ^ r` modulo `2 ^ (r + 1)`. -/
theorem two_pow_mul_odd_mod (r s : ℕ) : 2 ^ r * (2 * s + 1) % 2 ^ (r + 1) = 2 ^ r := by
  have h : 2 ^ r * (2 * s + 1) = 2 ^ (r + 1) * s + 2 ^ r := by ring
  rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]

/-- If `4 ∣ m` and the exact power of `2` in `m` is none of `2 ^ 2, ..., 2 ^ 10`, it is at least `2 ^ 11`. -/
theorem v2_large {m k t : ℕ} (ht : Odd t) (hm : m = 2 ^ k * t) (h4 : m % 4 = 0)
    (h8 : m % 8 ≠ 4) (h16 : m % 16 ≠ 8) (h32 : m % 32 ≠ 16) (h64 : m % 64 ≠ 32)
    (h128 : m % 128 ≠ 64) (h256 : m % 256 ≠ 128) (h512 : m % 512 ≠ 256) (h1024 : m % 1024 ≠ 512)
    (h2048 : m % 2048 ≠ 1024) : 11 ≤ k := by
  obtain ⟨s, rfl⟩ := ht
  have key := two_pow_mul_odd_mod k s
  rw [← hm] at key
  by_contra hk
  have hk' : k < 11 := by omega
  clear hk hm
  interval_cases k
  · have h2 : m % 2 = 1 := by simpa using key
    have h := Nat.mod_mod_of_dvd m (show 2 ∣ 4 by norm_num)
    rw [h4, h2] at h
    exact absurd h (by norm_num)
  · have h2 : m % 4 = 2 := by simpa using key
    rw [h4] at h2
    exact absurd h2 (by norm_num)
  · exact h8 (by simpa using key)
  · exact h16 (by simpa using key)
  · exact h32 (by simpa using key)
  · exact h64 (by simpa using key)
  · exact h128 (by simpa using key)
  · exact h256 (by simpa using key)
  · exact h512 (by simpa using key)
  · exact h1024 (by simpa using key)
  · exact h2048 (by simpa using key)

/-- `(1 + z ^ e) / z ^ e` decreases in `z` and `e`. -/
theorem kk_le {z e a b : ℕ} (ha : 1 ≤ a) (hz : a ≤ z) (he : b ≤ e) :
    (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) ≤ ((1 + a ^ b : ℕ) : ℚ) / ((a ^ b : ℕ) : ℚ) := by
  have hab : a ^ b ≤ z ^ e :=
    (Nat.pow_le_pow_left hz b).trans (Nat.pow_le_pow_right (by omega) he)
  have ha0 : 0 < a ^ b := pow_pos (by omega) b
  have hab' : ((a ^ b : ℕ) : ℚ) ≤ ((z ^ e : ℕ) : ℚ) := by exact_mod_cast hab
  have ha0' : (0 : ℚ) < ((a ^ b : ℕ) : ℚ) := by exact_mod_cast ha0
  rw [div_le_div_iff₀ (lt_of_lt_of_le ha0' hab') ha0', Nat.cast_add, Nat.cast_add, Nat.cast_one]
  linarith

/-- The weights argument when `3` is pinned: some simple prime `q ≥ 4097` has `3 ∣ q + 1`. The weight of `3`
is `(4/3)(4098/4096)`; `7` and `31` have the weights `b7`, `b31`, which may be below the default when the
prime is not simple or has no consumer. -/
theorem pinned_master {m e z q : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz5 : 5 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hqP : q ∈ P) (h3q : 3 ∣ q + 1) (hq : 4097 ≤ q) (b7 b31 : ℚ)
    (h7 : 1 ≤ b7 ∧ (7 ∈ P → 8 / 7 ≤ b7 ∧ b7 ≤ 4 / 3 ∧ (b7 ≠ 4 / 3 → ∀ p ∈ P, ¬ 7 ∣ p + 1)))
    (h31 : 1 ≤ b31 ∧
      (31 ∈ P → 32 / 31 ≤ b31 ∧ b31 ≤ 16 / 15 ∧ (b31 ≠ 16 / 15 → ∀ p ∈ P, ¬ 31 ∣ p + 1))) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ((4 / 3 * (4098 / 4096) * b7 * b31 * (64 / 63) * (2048 / 2047)) *
          ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, F3, -, -, -, -, -⟩ := facts hP hK E
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  obtain ⟨β, hβ3, hβ7, hβ31, hβ⟩ : ∃ β : ℕ → ℚ, β 3 = 4 / 3 * (4098 / 4096) ∧ β 7 = b7 ∧
      β 31 = b31 ∧ ∀ x : ℕ, x ≠ 3 → x ≠ 7 → x ≠ 31 → β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = 3 then 4 / 3 * (4098 / 4096) else if x = 7 then b7 else if x = 31 then b31
      else ((x : ℚ) + 1) / ((x : ℚ) - 1), by simp, by simp, by simp,
      fun x h1 h2 h3 => by simp [h1, h2, h3]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases h1 : p = 3
    · subst h1
      rw [hβ3]
      norm_num
    by_cases h2 : p = 7
    · subst h2
      obtain ⟨hlo, hhi, -⟩ := h7.2 hp
      rw [hβ7]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases h3 : p = 31
    · subst h3
      obtain ⟨hlo, hhi, -⟩ := h31.2 hp
      rw [hβ31]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    rw [hβ p h1 h2 h3]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → c = 3 ∨ c = 7 ∨ c = 31 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (hβ c hcon.1 hcon.2.1 hcon.2.2)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne
    rcases hsp c hne with rfl | rfl | rfl
    · have hpq : p = q := F3 3 Nat.prime_three (by norm_num) h3z p hp q hqP hd h3q
      rw [hpq, hβ q (by omega) (by omega) (by omega), hβ3]
      have hB := B_anti (a := 4097) (b := q) (by norm_num) hq
      have e1 : (((4097 : ℕ) : ℚ) + 1) / (((4097 : ℕ) : ℚ) - 1) = 4098 / 4096 := by norm_num
      have e2 : (1 + 1 / ((3 : ℕ) : ℚ)) = 4 / 3 := by norm_num
      rw [e1] at hB
      rw [e2]
      exact mul_le_mul_of_nonneg_left hB (by norm_num)
    · have hne' : b7 ≠ 4 / 3 := by
        intro hb
        apply hne
        rw [hβ7, hb]
        norm_num
      exact absurd hd ((h7.2 hc).2.2 hne' p hp)
    · have hne' : b31 ≠ 16 / 15 := by
        intro hb
        apply hne
        rw [hβ31, hb]
        norm_num
      exact absurd hd ((h31.2 hc).2.2 hne' p hp)
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hd127 := hβ 127 (by norm_num) (by norm_num) (by norm_num)
  have e127 : (((127 : ℕ) : ℚ) + 1) / (((127 : ℕ) : ℚ) - 1) = 64 / 63 := by norm_num
  rw [e127] at hd127
  have hM : ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hβ31, hd127]
      exact ⟨by norm_num, h7.1, h31.1, by norm_num⟩
  rw [hβ3, hβ7, hβ31, hd127] at hM
  have hZ : ∏ x ∈ L.filter (fun x => z ∣ x + 1), β x ≤
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod (fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp hx).1)
  have hM0 : (0 : ℚ) ≤ ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x :=
    Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le
  have hZ0 : (0 : ℚ) ≤ ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le
  have hX : ∏ x ∈ L, β x ≤ (4 / 3 * (4098 / 4096) * b7 * b31 * (64 / 63) * (2048 / 2047)) *
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => z ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by
        have := h7.1
        have := h31.1
        positivity)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- The leaves `x` with `x + 1 = 2 ^ k * z ^ j`, `j ≥ 1`, weigh at most `z^2/(z^2-3) * z/(z-2)`. -/
theorem zleaves_generic {z : ℕ} (hz : z.Prime) (hz5 : 5 ≤ z) {L : Finset ℕ}
    (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) :
    ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) * ((z : ℚ) / ((z : ℚ) - 2)) := by
  classical
  have hzpow : ∀ k : ℕ, ¬ z ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow h)
    omega
  have hform : ∀ x ∈ L.filter (fun x => z ∣ x + 1),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * z ^ j := by
    intro x hx
    obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := z) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have hzo : Odd (z ^ j) := Odd.pow (hz.odd_of_ne_two (by omega))
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at hzo
      rcases hodd with ⟨u, hu⟩
      rcases hzo with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hxz
      exact hzpow k hxz
  have hB0 : ∀ x ∈ L, (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x hx).1.one_lt.le
  have hA : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => z ^ 2 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) :=
    zleaf_bound (z := z) (by omega) 2 (by norm_num) _ (fun x hx => by
      obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
      obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
      refine ⟨k, j, hk, ?_, hkj⟩
      by_contra hj2
      have hj1 : j = 1 := by omega
      subst hj1
      rw [hkj, pow_one, pow_two] at hzz
      exact hzpow k (Nat.dvd_of_mul_dvd_mul_right hz.pos hzz))
  have hB' : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ z ^ 2 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (z : ℚ) / ((z : ℚ) - 2) :=
    fiber_bound (u := z) (by omega) _ (fun x hx => by
      obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
      obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
      refine ⟨k, hk, ?_⟩
      have hj1 : j = 1 := by
        by_contra hne
        apply hzz
        rw [hkj]
        exact Dvd.dvd.mul_left (pow_dvd_pow z (by omega)) _
      rw [hkj, hj1, pow_one])
  rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => z ∣ x + 1))
    (fun x => z ^ 2 ∣ x + 1)]
  refine mul_le_mul hA hB' (Finset.prod_nonneg fun x hx => ?_) ?_
  · exact hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  · have h5 : (5 : ℚ) ≤ z := by exact_mod_cast hz5
    exact div_nonneg (by positivity) (by nlinarith)

/-- Numeric end of a pinned weights argument. -/
theorem pinned_close {m : ℕ} {KK C Z KKb Zb : ℚ} (hm : 11 ≤ m)
    (hmain : (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * KK * (C * Z))
    (hKK0 : 0 ≤ KK) (hKK : KK ≤ KKb) (hC : 0 ≤ C) (hZ0 : 0 ≤ Z) (hZ : Z ≤ Zb)
    (hnum : (1 + 1 / (2 : ℚ) ^ 11) * KKb * (C * Zb) < 2) : False := by
  have hpow : (1 : ℚ) / 2 ^ m ≤ 1 / 2 ^ 11 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hm)
  have h1 : (1 + 1 / (2 : ℚ) ^ m) * KK * (C * Z) ≤ (1 + 1 / (2 : ℚ) ^ 11) * KKb * (C * Zb) := by
    apply mul_le_mul _ (mul_le_mul_of_nonneg_left hZ hC) (mul_nonneg hC hZ0) _
    · exact mul_le_mul (by linarith) hKK hKK0 (by positivity)
    · exact mul_nonneg (by positivity) (hKK0.trans hKK)
  linarith

/-- `3` pinned, `z ≥ 61`: no solution. Default weights; total at most `1.9968`. -/
theorem pinned_generic {m e z q : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz61 : 61 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hqP : q ∈ P) (h3q : 3 ∣ q + 1) (hq : 4097 ≤ q) (hm : 11 ≤ m) (he : 2 ≤ e) : False := by
  obtain ⟨L, hLP, hleaf, hmain⟩ := pinned_master hP hz (by omega) E hqP h3q hq (4 / 3) (16 / 15)
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
  have hZ := zleaves_generic hz (by omega) (fun x hx => hP x (hLP hx)) hleaf
  have hz' : (61 : ℚ) ≤ z := by exact_mod_cast hz61
  have h1 : (z : ℚ) / ((z : ℚ) - 2) ≤ 61 / 59 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2 : (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) ≤ 3721 / 3718 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  have h20 : (0 : ℚ) ≤ (z : ℚ) / ((z : ℚ) - 2) := div_nonneg (by positivity) (by linarith)
  refine pinned_close hm hmain (by positivity)
    (kk_le (a := 61) (b := 2) (by norm_num) hz61 he) (by norm_num)
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le)
    (hZ.trans (mul_le_mul h2 h1 h20 (by norm_num))) ?_
  norm_num

/-- The balance equation in rational form (the identity inside `master_gen`). -/
theorem balance_q {m K K' : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hK0 : 0 < K)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) :
    (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
  have hcast : ((2 : ℚ) ^ m + 1) * K' * ∏ p ∈ P, ((p : ℚ) + 1) =
      2 ^ (m + 1) * K * ∏ p ∈ P, (p : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) E
    push_cast at h
    exact h
  have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
    field_simp
  have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
  rw [e]
  field_simp
  rw [pow_succ] at hcast
  linarith

/-- Simple primes whose product of `1 + 1/p` is at least `2` cannot all occur: the product over all simple
primes is below `2`. -/
theorem lower_kill {m e z : ℕ} {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hS : S ⊆ P) (h2 : (2 : ℚ) ≤ ∏ p ∈ S, (1 + 1 / (p : ℚ))) : False := by
  have hb := balance_q hP (pow_pos hz.pos e) E
  have hle : ∏ p ∈ S, (1 + 1 / (p : ℚ)) ≤ ∏ p ∈ P, (1 + 1 / (p : ℚ)) :=
    Finset.prod_le_prod_of_subset_of_one_le hS (fun p _ => by positivity) (fun p _ _ => by
      have : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
      linarith)
  have ht : (0 : ℚ) < 1 / (2 : ℚ) ^ m := by positivity
  have hzq : (0 : ℚ) < ((z ^ e : ℕ) : ℚ) := by exact_mod_cast pow_pos hz.pos e
  have hK : (1 : ℚ) ≤ ((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ) := by
    rw [le_div_iff₀ hzq, Nat.cast_add, Nat.cast_one]
    linarith
  have hP2 : (2 : ℚ) ≤ ∏ p ∈ P, (1 + 1 / (p : ℚ)) := h2.trans hle
  have h3 : (1 + 1 / (2 : ℚ) ^ m) * 1 ≤
      (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) :=
    mul_le_mul_of_nonneg_left hK (by linarith)
  have h4 : (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) * 2 ≤
      (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ∏ p ∈ P, (1 + 1 / (p : ℚ)) :=
    mul_le_mul_of_nonneg_left hP2 (by positivity)
  linarith

/-- `a = 2 (mod 4)`: `5` divides `2 ^ a + 1`. -/
theorem five_dvd_two_pow_add_one {m : ℕ} (hm : m % 4 = 2) : 5 ∣ 2 ^ m + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 2 := ⟨m / 4, by omega⟩
  have h : (2 ^ (4 * j + 2) + 1) % 5 = 0 := by
    rw [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact Nat.dvd_of_mod_eq_zero h

/-- `a = 2 (mod 4)`: `5` is a simple prime with source `2 ^ a + 1`, so no simple prime `p` has `5 ∣ p + 1`;
`3` is a simple prime and `5` is the only simple prime `p` with `3 ∣ p + 1`. -/
theorem setup5 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz7 : 7 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hm : m % 4 = 2) :
    3 ∈ P ∧ 5 ∈ P ∧ (∀ p ∈ P, ¬ 5 ∣ p + 1) ∧ (∀ p ∈ P, 3 ∣ p + 1 → p = 5) := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨F1, F2, F3, F4, -, -, -, -⟩ := facts hP hK E
  have h5z : (5 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have h5 : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm
  have h5P : 5 ∈ P := F2 5 (by norm_num) (by norm_num) h5z h5
  have h3P : 3 ∈ P := F1 3 Nat.prime_three (by norm_num) h3z 5 h5P (by norm_num)
  exact ⟨h3P, h5P, F4 5 (by norm_num) (by norm_num) h5z h5,
    fun p hp h3 => F3 3 Nat.prime_three (by norm_num) h3z p hp 5 h5P h3 (by norm_num)⟩

/-- Kept parents of `7` (least odd prime factor other than `z`, `z ≥ 17`): `13`, or at least `181`. -/
theorem nx7 {z p : ℕ} (hz : 17 ≤ z) (hp : p.Prime) (hd : 7 ∣ p + 1) (hsq : ¬ 7 * 7 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 7 ≤ c') :
    p = 13 ∨ 181 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h5z : (5 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 26 := by omega
  obtain rfl : p = 7 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)
    | (have := hl 5 (by norm_num) (by norm_num) h5z (by decide); omega)

/-- Kept parents of `13`: `103`, or at least `883`. -/
theorem nx13 {z p : ℕ} (hz : 17 ≤ z) (hp : p.Prime) (hd : 13 ∣ p + 1) (hsq : ¬ 13 * 13 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 13 ≤ c') :
    p = 103 ∨ 883 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h7z : (7 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h11z : (11 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 68 := by omega
  obtain rfl : p = 13 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) h7z (by decide); omega)
    | (have := hl 11 (by norm_num) (by norm_num) h11z (by decide); omega)

/-- Kept parents of `31`: `61`, or at least `991`. -/
theorem nx31 {z p : ℕ} (hz : 17 ≤ z) (hp : p.Prime) (hd : 31 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 31 ≤ c') :
    p = 61 ∨ 991 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h5z : (5 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h7z : (7 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 32 := by omega
  obtain rfl : p = 31 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)
    | (have := hl 5 (by norm_num) (by norm_num) h5z (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) h7z (by decide); omega)

/-- A prime `p` with `61 ∣ p + 1` is at least `487`. -/
theorem nx61 {p : ℕ} (hp : p.Prime) (hd : 61 ∣ p + 1) : 487 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 61 * k - 1 := by omega
  interval_cases k <;> first | omega | (norm_num at hp)

/-- Kept parents of `103` are at least `823`. -/
theorem nx103 {z p : ℕ} (hz : 17 ≤ z) (hp : p.Prime) (hd : 103 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 103 ≤ c') :
    823 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 103 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)

/-- Kept parents of `127` are at least `4063`. -/
theorem nx127 {z p : ℕ} (hz : 17 ≤ z) (hp : p.Prime) (hd : 127 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    4063 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h5z : (5 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h7z : (7 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h13z : (13 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 32 := by omega
  obtain rfl : p = 127 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)
    | (have := hl 5 (by norm_num) (by norm_num) h5z (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) h7z (by decide); omega)
    | (have := hl 13 (by norm_num) (by norm_num) h13z (by decide); omega)

/-- One step of a weight chain: a kept parent `p ≥ N` of `c`. -/
theorem far_step {c N p : ℕ} {wp bc : ℚ} (hN : 2 ≤ N) (hNp : N ≤ p)
    (hwp : wp ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (hw : (1 + 1 / (c : ℚ)) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ≤ bc) :
    (1 + 1 / (c : ℚ)) * wp ≤ bc :=
  (mul_le_mul_of_nonneg_left (hwp.trans (B_anti hN hNp)) (by positivity)).trans hw

/-- The weights argument for `a = 2 (mod 4)`: `5` is a simple prime without consumer and the only simple prime
`p` with `3 ∣ p + 1`, so `3` weighs `(4/3)(6/5) = 8/5`. The primes `7, 13, 31, 61, 103, 127` have weights
`b7, ..., b127`; each is `≥ 1`, and when the prime is simple its weight is the default `(c+1)/(c-1)`, or the
prime has no consumer, or its consumer is the next prime of the chain `7 ← 13 ← 103`, `31 ← 61`, or its kept
parents are large (`nx7`, `nx13`, `nx31`, `nx61`, `nx103`, `nx127`). -/
theorem table_master {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz17 : 17 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hzP : z ∉ P) (h5P : 5 ∈ P) (h5c : ∀ p ∈ P, ¬ 5 ∣ p + 1) (b7 b13 b31 b61 b103 b127 : ℚ)
    (h7 : 1 ≤ b7 ∧ (7 ∈ P → 8 / 7 ≤ b7 ∧ b7 ≤ 4 / 3 ∧ (b7 = 4 / 3 ∨ (∀ p ∈ P, ¬ 7 ∣ p + 1) ∨
      (13 ∈ P ∧ 8 / 7 * b13 ≤ b7) ∨ (13 ∉ P ∧ 8 / 7 * (182 / 180) ≤ b7))))
    (h13 : 1 ≤ b13 ∧ (13 ∈ P → 14 / 13 ≤ b13 ∧ b13 ≤ 7 / 6 ∧ (b13 = 7 / 6 ∨
      (∀ p ∈ P, ¬ 13 ∣ p + 1) ∨ (103 ∈ P ∧ 14 / 13 * b103 ≤ b13) ∨
      (103 ∉ P ∧ 14 / 13 * (884 / 882) ≤ b13))))
    (h31 : 1 ≤ b31 ∧ (31 ∈ P → 32 / 31 ≤ b31 ∧ b31 ≤ 16 / 15 ∧ (b31 = 16 / 15 ∨
      (∀ p ∈ P, ¬ 31 ∣ p + 1) ∨ (61 ∈ P ∧ 32 / 31 * b61 ≤ b31) ∨
      (61 ∉ P ∧ 32 / 31 * (992 / 990) ≤ b31))))
    (h61 : 1 ≤ b61 ∧ (61 ∈ P → 62 / 61 ≤ b61 ∧ b61 ≤ 31 / 30 ∧ (b61 = 31 / 30 ∨
      (∀ p ∈ P, ¬ 61 ∣ p + 1) ∨ 62 / 61 * (488 / 486) ≤ b61)))
    (h103 : 1 ≤ b103 ∧ (103 ∈ P → 104 / 103 ≤ b103 ∧ b103 ≤ 52 / 51 ∧ (b103 = 52 / 51 ∨
      (∀ p ∈ P, ¬ 103 ∣ p + 1) ∨ 104 / 103 * (824 / 822) ≤ b103)))
    (h127 : 1 ≤ b127 ∧ (127 ∈ P → 128 / 127 ≤ b127 ∧ b127 ≤ 64 / 63 ∧ (b127 = 64 / 63 ∨
      (∀ p ∈ P, ¬ 127 ∣ p + 1) ∨ 128 / 127 * (4064 / 4062) ≤ b127))) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ((8 / 5 * b7 * b31 * b127 * (2048 / 2047)) *
          ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, F3, -, -, F6, -, -⟩ := facts hP hK E
  have hcz : ∀ c ∈ P, c ∉ ({z} : Finset ℕ) := fun c hc => by
    rw [Finset.mem_singleton]
    rintro rfl
    exact hzP hc
  obtain ⟨β, hβ3, hβ5, hβ7, hβ13, hβ31, hβ61, hβ103, hβ127, hβ⟩ : ∃ β : ℕ → ℚ, β 3 = 8 / 5 ∧
      β 5 = 6 / 5 ∧ β 7 = b7 ∧ β 13 = b13 ∧ β 31 = b31 ∧ β 61 = b61 ∧ β 103 = b103 ∧ β 127 = b127 ∧
      ∀ x : ℕ, x ≠ 3 → x ≠ 5 → x ≠ 7 → x ≠ 13 → x ≠ 31 → x ≠ 61 → x ≠ 103 → x ≠ 127 →
        β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = 3 then 8 / 5 else if x = 5 then 6 / 5 else if x = 7 then b7
      else if x = 13 then b13 else if x = 31 then b31 else if x = 61 then b61
      else if x = 103 then b103 else if x = 127 then b127 else ((x : ℚ) + 1) / ((x : ℚ) - 1),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      fun x h1 h2 h3 h4 h5 h6 h7 h8 => by simp [h1, h2, h3, h4, h5, h6, h7, h8]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [hβ3]
      norm_num
    by_cases e5 : p = 5
    · subst e5
      rw [hβ5]
      norm_num
    by_cases e7 : p = 7
    · subst e7
      obtain ⟨hlo, hhi, -⟩ := h7.2 hp
      rw [hβ7]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e13 : p = 13
    · subst e13
      obtain ⟨hlo, hhi, -⟩ := h13.2 hp
      rw [hβ13]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e31 : p = 31
    · subst e31
      obtain ⟨hlo, hhi, -⟩ := h31.2 hp
      rw [hβ31]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e61 : p = 61
    · subst e61
      obtain ⟨hlo, hhi, -⟩ := h61.2 hp
      rw [hβ61]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e103 : p = 103
    · subst e103
      obtain ⟨hlo, hhi, -⟩ := h103.2 hp
      rw [hβ103]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e127 : p = 127
    · subst e127
      obtain ⟨hlo, hhi, -⟩ := h127.2 hp
      rw [hβ127]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    rw [hβ p e3 e5 e7 e13 e31 e61 e103 e127]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) →
      c = 3 ∨ c = 5 ∨ c = 7 ∨ c = 13 ∨ c = 31 ∨ c = 61 ∨ c = 103 ∨ c = 127 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (hβ c hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2.1 hcon.2.2.2.2.1 hcon.2.2.2.2.2.1
      hcon.2.2.2.2.2.2.1 hcon.2.2.2.2.2.2.2)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne
    have hpp := (hP p hp).1
    have hwp := (hBd p hp).2
    rcases hsp c hne with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hp5 : p = 5 :=
        F3 3 Nat.prime_three (by norm_num) (hcz 3 hc) p hp 5 h5P hd (by norm_num)
      rw [hp5, hβ5, hβ3]
      norm_num
    · exact absurd hd (h5c p hp)
    · obtain ⟨-, -, hmenu⟩ := h7.2 hc
      rw [hβ7]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ7, heq]; norm_num) hne
      · exact absurd hd (hcl p hp)
      · have hpn : p = 13 :=
          F3 7 (by norm_num) (by norm_num) (hcz 7 hc) p hp 13 hnP hd (by norm_num)
        rw [hpn, hβ13]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx7 hz17 hpp hd (F6 7 (by norm_num) (by norm_num) (hcz 7 hc) p hp) hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 7) (N := 181) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h13.2 hc
      rw [hβ13]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ13, heq]; norm_num) hne
      · exact absurd hd (hcl p hp)
      · have hpn : p = 103 :=
          F3 13 (by norm_num) (by norm_num) (hcz 13 hc) p hp 103 hnP hd (by norm_num)
        rw [hpn, hβ103]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx13 hz17 hpp hd (F6 13 (by norm_num) (by norm_num) (hcz 13 hc) p hp) hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 13) (N := 883) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h31.2 hc
      rw [hβ31]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ31, heq]; norm_num) hne
      · exact absurd hd (hcl p hp)
      · have hpn : p = 61 :=
          F3 31 (by norm_num) (by norm_num) (hcz 31 hc) p hp 61 hnP hd (by norm_num)
        rw [hpn, hβ61]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx31 hz17 hpp hd hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 31) (N := 991) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h61.2 hc
      rw [hβ61]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ61, heq]; norm_num) hne
      · exact absurd hd (hcl p hp)
      · exact far_step (c := 61) (N := 487) (by norm_num) (nx61 hpp hd) hwp
          (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h103.2 hc
      rw [hβ103]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ103, heq]; norm_num) hne
      · exact absurd hd (hcl p hp)
      · exact far_step (c := 103) (N := 823) (by norm_num) (nx103 hz17 hpp hd hl) hwp
          (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h127.2 hc
      rw [hβ127]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ127, heq]; norm_num) hne
      · exact absurd hd (hcl p hp)
      · exact far_step (c := 127) (N := 4063) (by norm_num) (nx127 hz17 hpp hd hl) hwp
          (le_trans (le_of_eq (by norm_num)) hw)
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hM : ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hβ31, hβ127]
      exact ⟨by norm_num, h7.1, h31.1, h127.1⟩
  rw [hβ3, hβ7, hβ31, hβ127] at hM
  have hZ : ∏ x ∈ L.filter (fun x => z ∣ x + 1), β x ≤
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod (fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp hx).1)
  have hX : ∏ x ∈ L, β x ≤ (8 / 5 * b7 * b31 * b127 * (2048 / 2047)) *
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => z ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by
        have := h7.1
        have := h31.1
        have := h127.1
        positivity)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- Numeric end of a weights argument, for `a ≥ a0`. -/
theorem table_close {m a0 : ℕ} {KK C Z KKb Zb : ℚ} (hm : a0 ≤ m)
    (hmain : (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * KK * (C * Z))
    (hKK0 : 0 ≤ KK) (hKK : KK ≤ KKb) (hC : 0 ≤ C) (hZ0 : 0 ≤ Z) (hZ : Z ≤ Zb)
    (hnum : (1 + 1 / (2 : ℚ) ^ a0) * KKb * (C * Zb) < 2) : False := by
  have hpow : (1 : ℚ) / 2 ^ m ≤ 1 / 2 ^ a0 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hm)
  have h1 : (1 + 1 / (2 : ℚ) ^ m) * KK * (C * Z) ≤ (1 + 1 / (2 : ℚ) ^ a0) * KKb * (C * Zb) := by
    apply mul_le_mul _ (mul_le_mul_of_nonneg_left hZ hC) (mul_nonneg hC hZ0) _
    · exact mul_le_mul (by linarith) hKK hKK0 (by positivity)
    · exact mul_nonneg (by positivity) (hKK0.trans hKK)
  linarith

/-- End of a weights argument for `z ≥ Z0`, `a ≥ a0`, `e ≥ e0`: the leaves `x` with `z ∣ x + 1` weigh at most
`Z0^2/(Z0^2-3) * Z0/(Z0-2)` (`zleaves_generic`). -/
theorem table_finish {m e z a0 Z0 e0 : ℕ} {P : Finset ℕ} {C : ℚ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime) (hZ5 : 5 ≤ Z0) (hzZ : Z0 ≤ z) (hm : a0 ≤ m) (he : e0 ≤ e) (hC : 0 ≤ C)
    (hex : ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        (C * ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1))))
    (hnum : (1 + 1 / (2 : ℚ) ^ a0) * (((1 + Z0 ^ e0 : ℕ) : ℚ) / ((Z0 ^ e0 : ℕ) : ℚ)) *
      (C * (((Z0 : ℚ) ^ 2 / ((Z0 : ℚ) ^ 2 - 3)) * ((Z0 : ℚ) / ((Z0 : ℚ) - 2)))) < 2) : False := by
  obtain ⟨L, hLP, hleaf, hmain⟩ := hex
  have hZ := zleaves_generic hz (by omega) (fun x hx => hP x (hLP hx)) hleaf
  have h5 : (5 : ℚ) ≤ (Z0 : ℚ) := by exact_mod_cast hZ5
  have hzq : (Z0 : ℚ) ≤ (z : ℚ) := by exact_mod_cast hzZ
  have h1 : (z : ℚ) / ((z : ℚ) - 2) ≤ (Z0 : ℚ) / ((Z0 : ℚ) - 2) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) ≤ (Z0 : ℚ) ^ 2 / ((Z0 : ℚ) ^ 2 - 3) := by
    rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith
  have h10 : (0 : ℚ) ≤ (z : ℚ) / ((z : ℚ) - 2) := div_nonneg (by linarith) (by linarith)
  have h20 : (0 : ℚ) ≤ (Z0 : ℚ) ^ 2 / ((Z0 : ℚ) ^ 2 - 3) := div_nonneg (by positivity) (by nlinarith)
  exact table_close hm hmain (by positivity) (kk_le (by omega) hzZ he) hC
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le)
    (hZ.trans (mul_le_mul h2 h1 h10 h20)) hnum

/-- `3, 5, 7, 13, 31` cannot all be simple primes: `(4/3)(6/5)(8/7)(14/13)(32/31) > 2`. -/
theorem kill_7_13_31 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (h3 : 3 ∈ P) (h5 : 5 ∈ P) (h7 : 7 ∈ P) (h13 : 13 ∈ P) (h31 : 31 ∈ P) : False := by
  refine lower_kill hP hz E (S := {3, 5, 7, 13, 31}) ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num

/-- `3, 5, 7, 13, 103, 127` cannot all be simple primes: the product of `1 + 1/p` is above `2`. -/
theorem kill_7_13_103_127 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (h3 : 3 ∈ P) (h5 : 5 ∈ P) (h7 : 7 ∈ P) (h13 : 13 ∈ P) (h103 : 103 ∈ P) (h127 : 127 ∈ P) :
    False := by
  refine lower_kill hP hz E (S := {3, 5, 7, 13, 103, 127}) ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num

/-- `a = 2 (mod 4)`, `a ≥ 22`, `e ≥ 3`, `z ≥ 823`: no solution. Cases on which of `13, 31, 103, 127` are
simple primes; totals at most `1.99903`. -/
theorem amod4_large {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz823 : 823 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hzP : z ∉ P) (hm4 : m % 4 = 2) (hm : 22 ≤ m) (he : 3 ≤ e) : False := by
  classical
  obtain ⟨h3P, h5P, h5c, -⟩ := setup5 hP hz (by omega) E hm4
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨F1, -, -, -, -, -, -, -⟩ := facts hP hK E
  have h7z : (7 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  by_cases h13 : 13 ∈ P
  · have h7 : 7 ∈ P := F1 7 (by norm_num) (by norm_num) h7z 13 h13 (by norm_num)
    by_cases h31 : 31 ∈ P
    · exact kill_7_13_31 hP hz E h3P h5P h7 h13 h31
    · by_cases h103 : 103 ∈ P
      · by_cases h127 : 127 ∈ P
        · exact kill_7_13_103_127 hP hz E h3P h5P h7 h13 h103 h127
        · -- 7 <- 13 <- 103, kept parents of 103 at least 823; 31 and 127 are not simple
          exact table_finish hP hz (by norm_num) hz823 hm he (by norm_num)
            (table_master hP hz (by omega) E hzP h5P h5c
              (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) (14 / 13 * (104 / 103 * (824 / 822))) 1
              (31 / 30) (104 / 103 * (824 / 822)) 1
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h103, le_refl _⟩))⟩⟩
              ⟨le_refl _, fun h => absurd h h31⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
              ⟨le_refl _, fun h => absurd h h127⟩)
            (by norm_num)
      · -- 7 <- 13, kept parents of 13 at least 883; 31 is not simple
        exact table_finish hP hz (by norm_num) hz823 hm he (by norm_num)
          (table_master hP hz (by omega) E hzP h5P h5c
            (8 / 7 * (14 / 13 * (884 / 882))) (14 / 13 * (884 / 882)) 1
            (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h103, le_refl _⟩))⟩⟩
            ⟨le_refl _, fun h => absurd h h31⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩)
          (by norm_num)
  · -- 13 is not simple: kept parents of 7 at least 181
    exact table_finish hP hz (by norm_num) hz823 hm he (by norm_num)
      (table_master hP hz (by omega) E hzP h5P h5c
        (8 / 7 * (182 / 180)) 1 (16 / 15)
        (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h13, le_refl _⟩))⟩⟩
        ⟨le_refl _, fun h => absurd h h13⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩)
      (by norm_num)

/-- If `2 ^ k * z - 1` is not prime for `1 ≤ k ≤ s`, the leaves `x` with `x + 1 = 2 ^ k * z ^ j`, `j ≥ 1`, weigh at
most `z^2/(z^2-3) * u/(u-2)` with `u = 2 ^ s * z`. -/
theorem zleaves_skip {z s : ℕ} (hz : z.Prime) (hz5 : 5 ≤ z)
    (hs : ∀ k : ℕ, 1 ≤ k → k ≤ s → ¬ (2 ^ k * z - 1).Prime) {L : Finset ℕ}
    (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) :
    ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) *
        (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)) := by
  classical
  have hzpow : ∀ k : ℕ, ¬ z ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow h)
    omega
  have hform : ∀ x ∈ L.filter (fun x => z ∣ x + 1),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * z ^ j := by
    intro x hx
    obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := z) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have hzo : Odd (z ^ j) := Odd.pow (hz.odd_of_ne_two (by omega))
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at hzo
      rcases hodd with ⟨u, hu⟩
      rcases hzo with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hxz
      exact hzpow k hxz
  have hB0 : ∀ x ∈ L, (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x hx).1.one_lt.le
  have hA : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => z ^ 2 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) :=
    zleaf_bound (z := z) (by omega) 2 (by norm_num) _ (fun x hx => by
      obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
      obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
      refine ⟨k, j, hk, ?_, hkj⟩
      by_contra hj2
      have hj1 : j = 1 := by omega
      subst hj1
      rw [hkj, pow_one, pow_two] at hzz
      exact hzpow k (Nat.dvd_of_mul_dvd_mul_right hz.pos hzz))
  have hB' : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ z ^ 2 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
        ((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2) :=
    fiber_bound (u := 2 ^ s * z)
      (le_trans (by omega : 3 ≤ z) (Nat.le_mul_of_pos_left z (pow_pos (by norm_num) s))) _
      (fun x hx => by
        obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        have hj1 : j = 1 := by
          by_contra hne
          apply hzz
          rw [hkj]
          exact Dvd.dvd.mul_left (pow_dvd_pow z (by omega)) _
        rw [hj1, pow_one] at hkj
        have hxL : x ∈ L := (Finset.mem_filter.mp hx1).1
        have hks : s < k := by
          by_contra hle
          have hx' : x = 2 ^ k * z - 1 := by omega
          exact hs k hk (by omega) (hx' ▸ (hLp x hxL).1)
        refine ⟨k - s, by omega, ?_⟩
        rw [hkj, ← mul_assoc, ← pow_add]
        congr 2
        omega)
  rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => z ∣ x + 1))
    (fun x => z ^ 2 ∣ x + 1)]
  refine mul_le_mul hA hB' (Finset.prod_nonneg fun x hx => ?_) ?_
  · exact hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  · have h5 : (5 : ℚ) ≤ z := by exact_mod_cast hz5
    exact div_nonneg (by positivity) (by nlinarith)

/-- End of a weights argument for one prime `z` with the leaf bound of `zleaves_skip`. -/
theorem table_finish_skip {m e z a0 e0 s : ℕ} {P : Finset ℕ} {C : ℚ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hz5 : 5 ≤ z)
    (hs : ∀ k : ℕ, 1 ≤ k → k ≤ s → ¬ (2 ^ k * z - 1).Prime)
    (hm : a0 ≤ m) (he : e0 ≤ e) (hC : 0 ≤ C)
    (hex : ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        (C * ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1))))
    (hnum : (1 + 1 / (2 : ℚ) ^ a0) * (((1 + z ^ e0 : ℕ) : ℚ) / ((z ^ e0 : ℕ) : ℚ)) *
      (C * (((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) *
        (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)))) < 2) : False := by
  obtain ⟨L, hLP, hleaf, hmain⟩ := hex
  have hZ := zleaves_skip hz hz5 hs (fun x hx => hP x (hLP hx)) hleaf
  exact table_close hm hmain (by positivity) (kk_le (by omega) (le_refl z) he) hC
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) hZ hnum

/-- `z = 7`: the leaves `x` with `x + 1 = 2 ^ k * 7 ^ j`, `j ≥ 1`, weigh at most `(49/46)(14/12)(112/110)`
(for `j = 1` only `13` is below `223`, since `27`, `55`, `111` are not prime). -/
theorem seven_leaves {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 7) :
    ∏ x ∈ L.filter (fun x => 7 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      (49 / 46) * ((14 / 12) * (112 / 110)) := by
  classical
  have hform : ∀ x ∈ L.filter (fun x => 7 ∣ x + 1), ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * 7 ^ j := by
    intro x hx
    obtain ⟨hxL, hx7⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := 7) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have h7 : Odd (7 ^ j) := Odd.pow (by decide)
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at h7
      rcases hodd with ⟨u, hu⟩
      rcases h7 with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hx7
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) Nat.prime_two).mp
        ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow hx7)
      omega
  have hB0 : ∀ x ∈ L, (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x hx).1.one_lt.le
  -- j ≥ 2
  have hA : ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => 49 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ 49 / 46 := by
    have h := zleaf_bound (z := 7) (by norm_num) 2 (by norm_num)
      ((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => 49 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx1, h49⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, j, hk, ?_, hkj⟩
        by_contra hj2
        have hj1 : j = 1 := by omega
        subst hj1
        rw [hkj, pow_one, show (49 : ℕ) = 7 * 7 by norm_num] at h49
        have h7 : 7 ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h49
        have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) Nat.prime_two).mp
          ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h7)
        omega)
    norm_num at h ⊢
    exact h
  -- j = 1
  have hj1 : ∀ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1),
      ∃ k, 1 ≤ k ∧ x + 1 = 2 ^ k * 7 := by
    intro x hx
    obtain ⟨hx1, h49⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
    refine ⟨k, hk, ?_⟩
    have hj1 : j = 1 := by
      by_contra hne
      apply h49
      rw [hkj, show (49 : ℕ) = 7 ^ 2 by norm_num]
      exact Dvd.dvd.mul_left (pow_dvd_pow 7 (by omega)) _
    rw [hkj, hj1, pow_one]
  have hsmall : ∏ x ∈ ((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1)).filter
      (fun x => x < 223), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ 14 / 12 := by
    have hsub : ((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1)).filter
        (fun x => x < 223) ⊆ ({13} : Finset ℕ) := by
      intro x hx
      obtain ⟨hx2, hlt⟩ := Finset.mem_filter.mp hx
      obtain ⟨k, hk, hkx⟩ := hj1 x hx2
      have hxL : x ∈ L := (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).1
      have hxp := (hLp x hxL).1
      have hk5 : k < 5 := by
        by_contra h5
        have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at this
        omega
      rw [Finset.mem_singleton]
      interval_cases k <;> norm_num at hkx <;>
        first
        | omega
        | (have hx' : x = 27 := by omega
           subst hx'; exact absurd hxp (by norm_num))
        | (have hx' : x = 55 := by omega
           subst hx'; exact absurd hxp (by norm_num))
        | (have hx' : x = 111 := by omega
           subst hx'; exact absurd hxp (by norm_num))
    have h := Finset.prod_le_prod_of_subset_of_one_le
      (f := fun x : ℕ => ((x : ℚ) + 1) / ((x : ℚ) - 1)) hsub
      (fun x hx => hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp
        (Finset.mem_filter.mp hx).1).1).1) (fun x hx _ => by
        rw [Finset.mem_singleton.mp hx]
        norm_num)
    rw [Finset.prod_singleton] at h
    norm_num at h ⊢
    exact h
  have hlarge : ∏ x ∈ ((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1)).filter
      (fun x => ¬ x < 223), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ 112 / 110 := by
    have h := fiber_bound (u := 112) (by norm_num)
      (((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1)).filter
        (fun x => ¬ x < 223)) (fun x hx => by
        obtain ⟨hx2, hge⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, hk, hkx⟩ := hj1 x hx2
        have hk5 : 5 ≤ k := by
          by_contra h5
          have : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
          norm_num at this
          omega
        refine ⟨k - 4, by omega, ?_⟩
        rw [hkx, show (112 : ℕ) = 2 ^ 4 * 7 by norm_num, ← mul_assoc, ← pow_add]
        congr 2
        omega)
    norm_num at h ⊢
    exact h
  have hB' : ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (14 / 12) * (112 / 110) := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      ((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1)) (fun x => x < 223)]
    refine mul_le_mul hsmall hlarge (Finset.prod_nonneg fun x hx => ?_) (by norm_num)
    exact hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1
  rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => 7 ∣ x + 1))
    (fun x => 49 ∣ x + 1)]
  refine mul_le_mul hA hB' (Finset.prod_nonneg fun x hx => ?_) (by norm_num)
  exact hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1

/-- `3` pinned, `z = 7` (so `7` is not a simple prime): no solution. Total at most `1.8683`. -/
theorem pinned_seven {m e q : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hzP : 7 ∉ P) (hqP : q ∈ P) (h3q : 3 ∣ q + 1) (hq : 4097 ≤ q) (hm : 11 ≤ m) (he : 2 ≤ e) :
    False := by
  have hz : Nat.Prime 7 := by norm_num
  obtain ⟨L, hLP, hleaf, hmain⟩ := pinned_master hP hz (by norm_num) E hqP h3q hq 1 (16 / 15)
    ⟨le_refl _, fun h => absurd h hzP⟩
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
  have hZ := seven_leaves (fun x hx => hP x (hLP hx)) hleaf
  refine pinned_close hm hmain (by positivity)
    (kk_le (a := 7) (b := 2) (by norm_num) (le_refl _) he) (by norm_num)
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) hZ ?_
  norm_num

/-- `3` pinned, `z = 31` (so `31` is not a simple prime): no solution. Total at most `1.9415`. -/
theorem pinned_thirtyone {m e q : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 31 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 31 ^ e * ∏ p ∈ P, p)
    (hzP : 31 ∉ P) (hqP : q ∈ P) (h3q : 3 ∣ q + 1) (hq : 4097 ≤ q) (hm : 11 ≤ m) (he : 2 ≤ e) :
    False := by
  have hz : Nat.Prime 31 := by norm_num
  obtain ⟨L, hLP, hleaf, hmain⟩ := pinned_master hP hz (by norm_num) E hqP h3q hq (4 / 3) 1
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
    ⟨le_refl _, fun h => absurd h hzP⟩
  have hZ := zleaves_generic hz (by norm_num) (fun x hx => hP x (hLP hx)) hleaf
  refine pinned_close hm hmain (by positivity)
    (kk_le (a := 31) (b := 2) (by norm_num) (le_refl _) he) (by norm_num)
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) hZ ?_
  norm_num

/-- A prime `p` with `13 ∣ p + 1` is at least `103`. -/
theorem nx13_103 {p : ℕ} (hp : p.Prime) (hd : 13 ∣ p + 1) : 103 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 13 * k - 1 := by omega
  interval_cases k <;> first | omega | (norm_num at hp)

/-- Core prime `7`: kept parents of `127` (least odd prime factor other than `7`) are at least `1777`. -/
theorem nx127_7 {p : ℕ} (hp : p.Prime) (hd : 127 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({7} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    1777 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 14 := by omega
  obtain rfl : p = 127 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)

/-- A fibre of leaves `x + 1 = 2 ^ k * u0` in which the only one with `k ≤ k0` is `q0`. -/
theorem fiber_split {u0 k0 q0 : ℕ} (hu : 3 ≤ u0) (hq0 : 2 ≤ q0) (S : Finset ℕ)
    (hS : ∀ x ∈ S, ∃ k, 1 ≤ k ∧ x + 1 = 2 ^ k * u0)
    (hsmall : ∀ x ∈ S, ∀ k, 1 ≤ k → k ≤ k0 → x + 1 = 2 ^ k * u0 → x = q0) :
    ∏ x ∈ S, (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      (((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) *
        (((2 ^ k0 * u0 : ℕ) : ℚ) / (((2 ^ k0 * u0 : ℕ) : ℚ) - 2)) := by
  classical
  have hB0 : ∀ x ∈ S, (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => by
    obtain ⟨k, hk, hkx⟩ := hS x hx
    have h2 : 2 ^ 1 * u0 ≤ 2 ^ k * u0 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk)
    exact B_nonneg (by omega)
  have h1 : ∏ x ∈ S.filter (fun x => x = q0), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((q0 : ℚ) + 1) / ((q0 : ℚ) - 1) := by
    have hsub : S.filter (fun x => x = q0) ⊆ ({q0} : Finset ℕ) := fun x hx => by
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hx).2
    have h := Finset.prod_le_prod_of_subset_of_one_le
      (f := fun x : ℕ => ((x : ℚ) + 1) / ((x : ℚ) - 1)) hsub
      (fun x hx => hB0 x (Finset.mem_filter.mp hx).1) (fun x hx _ => by
        rw [Finset.mem_singleton.mp hx]
        show (1 : ℚ) ≤ ((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)
        have h2 : (2 : ℚ) ≤ q0 := by exact_mod_cast hq0
        rw [le_div_iff₀ (by linarith)]
        linarith)
    rwa [Finset.prod_singleton] at h
  have h2 : ∏ x ∈ S.filter (fun x => ¬ x = q0), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((2 ^ k0 * u0 : ℕ) : ℚ) / (((2 ^ k0 * u0 : ℕ) : ℚ) - 2) :=
    fiber_bound (u := 2 ^ k0 * u0)
      (le_trans hu (Nat.le_mul_of_pos_left u0 (pow_pos (by norm_num) k0))) _ (fun x hx => by
        obtain ⟨hxS, hne⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, hk, hkx⟩ := hS x hxS
        have hk0 : k0 < k := by
          by_contra hle
          exact hne (hsmall x hxS k hk (by omega) hkx)
        refine ⟨k - k0, by omega, ?_⟩
        rw [hkx, ← mul_assoc, ← pow_add]
        congr 2
        omega)
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun x => x = q0)]
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun x hx => hB0 x (Finset.mem_filter.mp hx).1)
    (B_nonneg (by omega))

/-- Core prime `7`: the leaves `x ≠ 13` with `x + 1 = 2 ^ k * 7 ^ j`, `j ≥ 1`, weigh at most
`(343/340) (98/96)(392/390) (224/222)(224/222)`: for `j = 1` only `223` has `k ≤ 5` (`27, 55, 111` are not
prime), for `j = 2` only `97` has `k ≤ 3` (`195, 391` are not prime). -/
theorem seven_leaves2 {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 7) :
    ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      (343 / 340) * (((98 / 96) * (392 / 390)) * ((224 / 222) * (224 / 222))) := by
  classical
  have h7pow : ∀ k : ℕ, ¬ 7 ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
    omega
  have hmem : ∀ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
      x ∈ L ∧ 7 ∣ x + 1 ∧ ¬ x = 13 := fun x hx =>
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2, (Finset.mem_filter.mp hx).2⟩
  have hform : ∀ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * 7 ^ j := by
    intro x hx
    obtain ⟨hxL, hx7, -⟩ := hmem x hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := 7) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have h7 : Odd (7 ^ j) := Odd.pow (by decide)
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at h7
      rcases hodd with ⟨u, hu⟩
      rcases h7 with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hx7
      exact h7pow k hx7
  have hB0 : ∀ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
      (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x (hmem x hx).1).1.one_lt.le
  -- j ≥ 3
  have hA : ∏ x ∈ ((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13)).filter
      (fun x => 343 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ 343 / 340 := by
    have h := zleaf_bound (z := 7) (by norm_num) 3 (by norm_num)
      (((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13)).filter
        (fun x => 343 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx1, h343⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, j, hk, ?_, hkj⟩
        by_contra hj3
        have hj' : j = 1 ∨ j = 2 := by omega
        rcases hj' with rfl | rfl
        · rw [hkj, pow_one, show (343 : ℕ) = 49 * 7 by norm_num] at h343
          exact h7pow k ((by norm_num : (7 : ℕ) ∣ 49).trans
            (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h343))
        · rw [hkj, show (343 : ℕ) = 7 * 7 ^ 2 by norm_num] at h343
          exact h7pow k (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h343))
    norm_num at h ⊢
    exact h
  -- j = 2
  have hB2 : ∏ x ∈ (((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13)).filter
      (fun x => ¬ 343 ∣ x + 1)).filter (fun x => 49 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (98 / 96) * (392 / 390) := by
    have h := fiber_split (u0 := 49) (k0 := 3) (q0 := 97) (by norm_num) (by norm_num)
      ((((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13)).filter
        (fun x => ¬ 343 ∣ x + 1)).filter (fun x => 49 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx2, h49⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx1, h343⟩ := Finset.mem_filter.mp hx2
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, hk, ?_⟩
        have hj2 : j = 2 := by
          by_contra hne
          have hj' : j = 1 ∨ 3 ≤ j := by omega
          rcases hj' with rfl | hj3
          · rw [hkj, pow_one, show (49 : ℕ) = 7 * 7 by norm_num] at h49
            exact h7pow k (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h49)
          · apply h343
            rw [hkj, show (343 : ℕ) = 7 ^ 3 by norm_num]
            exact Dvd.dvd.mul_left (pow_dvd_pow 7 hj3) _
        rw [hkj, hj2]
        norm_num) (fun x hx k hk hk3 hkx => by
        have hxp := (hLp x (hmem x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1).1
        interval_cases k <;> norm_num at hkx <;>
          first
          | omega
          | (have hx' : x = 195 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 391 := by omega
             subst hx'; exact absurd hxp (by norm_num)))
    norm_num at h ⊢
    exact h
  -- j = 1
  have hB1 : ∏ x ∈ (((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13)).filter
      (fun x => ¬ 343 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (224 / 222) * (224 / 222) := by
    have h := fiber_split (u0 := 7) (k0 := 5) (q0 := 223) (by norm_num) (by norm_num)
      ((((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13)).filter
        (fun x => ¬ 343 ∣ x + 1)).filter (fun x => ¬ 49 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx2, h49⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx2
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, hk, ?_⟩
        have hj1 : j = 1 := by
          by_contra hne
          apply h49
          rw [hkj, show (49 : ℕ) = 7 ^ 2 by norm_num]
          exact Dvd.dvd.mul_left (pow_dvd_pow 7 (by omega)) _
        rw [hkj, hj1, pow_one]) (fun x hx k hk hk5 hkx => by
        have hx1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
        have hxp := (hLp x (hmem x hx1).1).1
        have hx13 := (hmem x hx1).2.2
        interval_cases k <;> norm_num at hkx <;>
          first
          | omega
          | (have hx' : x = 27 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 55 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 111 := by omega
             subst hx'; exact absurd hxp (by norm_num)))
    norm_num at h ⊢
    exact h
  rw [← Finset.prod_filter_mul_prod_filter_not
    ((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13)) (fun x => 343 ∣ x + 1)]
  refine mul_le_mul hA ?_ (Finset.prod_nonneg fun x hx => hB0 x (Finset.mem_filter.mp hx).1)
    (by norm_num)
  rw [← Finset.prod_filter_mul_prod_filter_not
    (((L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13)).filter
      (fun x => ¬ 343 ∣ x + 1)) (fun x => 49 ∣ x + 1)]
  exact mul_le_mul hB2 hB1 (Finset.prod_nonneg fun x hx =>
    hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1) (by norm_num)

/-- The weights argument for the core prime `7` and `a = 2 (mod 4)`: `3` weighs `8/5`, the leaf `13`
(`14 = 2 * 7`) weighs `(14/13)(104/102)` because its parents are at least `103`, and `127` weighs
`(128/127)(1778/1776)` because its kept parents are at least `1777`. -/
theorem seven_master {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hzP : 7 ∉ P) (h5P : 5 ∈ P) (h5c : ∀ p ∈ P, ¬ 5 ∣ p + 1) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 7) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + 7 ^ e : ℕ) : ℚ) / ((7 ^ e : ℕ) : ℚ)) *
        ((8 / 5 * 1 * (16 / 15) * (128 / 127 * (1778 / 1776)) * (2048 / 2047)) *
          ((14 / 13 * (104 / 102)) *
            ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
              (((x : ℚ) + 1) / ((x : ℚ) - 1)))) := by
  classical
  have hz : Nat.Prime 7 := by norm_num
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, F3, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨β, hβ3, hβ5, hβ7, hβ13, hβ127, hβ⟩ : ∃ β : ℕ → ℚ, β 3 = 8 / 5 ∧ β 5 = 6 / 5 ∧ β 7 = 1 ∧
      β 13 = 14 / 13 * (104 / 102) ∧ β 127 = 128 / 127 * (1778 / 1776) ∧
      ∀ x : ℕ, x ≠ 3 → x ≠ 5 → x ≠ 7 → x ≠ 13 → x ≠ 127 →
        β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = 3 then 8 / 5 else if x = 5 then 6 / 5 else if x = 7 then 1
      else if x = 13 then 14 / 13 * (104 / 102) else if x = 127 then 128 / 127 * (1778 / 1776)
      else ((x : ℚ) + 1) / ((x : ℚ) - 1), by simp, by simp, by simp, by simp, by simp,
      fun x h1 h2 h3 h4 h5 => by simp [h1, h2, h3, h4, h5]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [hβ3]
      norm_num
    by_cases e5 : p = 5
    · subst e5
      rw [hβ5]
      norm_num
    by_cases e7 : p = 7
    · subst e7
      exact absurd hp hzP
    by_cases e13 : p = 13
    · subst e13
      rw [hβ13]
      norm_num
    by_cases e127 : p = 127
    · subst e127
      rw [hβ127]
      norm_num
    rw [hβ p e3 e5 e7 e13 e127]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) →
      c = 3 ∨ c = 5 ∨ c = 7 ∨ c = 13 ∨ c = 127 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (hβ c hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2.1 hcon.2.2.2.2)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({7} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne
    have hpp := (hP p hp).1
    have hwp := (hBd p hp).2
    rcases hsp c hne with rfl | rfl | rfl | rfl | rfl
    · have hp5 : p = 5 := F3 3 Nat.prime_three (by norm_num) (by simp) p hp 5 h5P hd (by norm_num)
      rw [hp5, hβ5, hβ3]
      norm_num
    · exact absurd hd (h5c p hp)
    · exact absurd hc hzP
    · rw [hβ13]
      exact far_step (c := 13) (N := 103) (by norm_num) (nx13_103 hpp hd) hwp
        (le_of_eq (by norm_num))
    · rw [hβ127]
      exact far_step (c := 127) (N := 1777) (by norm_num) (nx127_7 hpp hd hl) hwp
        (le_of_eq (by norm_num))
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 7 := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hd31 := hβ 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : (((31 : ℕ) : ℚ) + 1) / (((31 : ℕ) : ℚ) - 1) = 16 / 15 := by norm_num
  rw [e31] at hd31
  have hM : ∏ x ∈ L.filter (fun x => ¬ 7 ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hd31, hβ127]
      norm_num
  rw [hβ3, hβ7, hd31, hβ127] at hM
  -- the leaves with 7 ∣ x + 1: the leaf 13 has its own weight
  have h13 : ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => x = 13), β x ≤
      14 / 13 * (104 / 102) := by
    have hsub : (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => x = 13) ⊆ ({13} : Finset ℕ) :=
      fun x hx => by
        rw [Finset.mem_singleton]
        exact (Finset.mem_filter.mp hx).2
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx _ => by
        rw [Finset.mem_singleton.mp hx, hβ13]
        norm_num)
    rwa [Finset.prod_singleton, hβ13] at h
  have hrest : ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13), β x ≤
      ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
  have hZ : ∏ x ∈ L.filter (fun x => 7 ∣ x + 1), β x ≤ (14 / 13 * (104 / 102)) *
      ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => 7 ∣ x + 1))
      (fun x => x = 13) β]
    exact mul_le_mul h13 hrest (Finset.prod_nonneg fun x hx =>
      (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le) (by norm_num)
  have hX : ∏ x ∈ L, β x ≤
      (8 / 5 * 1 * (16 / 15) * (128 / 127 * (1778 / 1776)) * (2048 / 2047)) *
        ((14 / 13 * (104 / 102)) *
          ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
            (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => 7 ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by norm_num)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- `z = 7`, `a = 2 (mod 4)`, `a ≥ 22`, `e ≥ 3`: no solution. Total at most `1.99950`. -/
theorem amod4_7 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hzP : 7 ∉ P) (hm4 : m % 4 = 2) (hm : 22 ≤ m) (he : 3 ≤ e) : False := by
  have hz : Nat.Prime 7 := by norm_num
  obtain ⟨-, h5P, h5c, -⟩ := setup5 hP hz (le_refl 7) E hm4
  obtain ⟨L, hLP, hleaf, hmain⟩ := seven_master hP E hzP h5P h5c
  have hZ := seven_leaves2 (fun x hx => hP x (hLP hx)) hleaf
  have hZ0 : (0 : ℚ) ≤ ∏ x ∈ (L.filter (fun x => 7 ∣ x + 1)).filter (fun x => ¬ x = 13),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_nonneg fun x hx => B_nonneg
      (hP x (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)).1.one_lt.le
  refine table_close hm hmain (by positivity)
    (kk_le (a := 7) (b := 3) (by norm_num) (le_refl _) he) (by norm_num)
    (mul_nonneg (by norm_num) hZ0) (mul_le_mul_of_nonneg_left hZ (by norm_num)) ?_
  norm_num

/-- Core prime `31`: the leaves `x ≠ 61` with `x + 1 = 2 ^ k * 31 ^ j`, `j ≥ 1`: for `j = 1` only `991` has
`k ≤ 6` (`123, 247, 495, 1983` are not prime), for `j = 2` only `7687` has `k ≤ 3` (`1921, 3843` are not prime). -/
theorem thirtyone_leaves {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 31) :
    ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      (29791 / 29788) * (((7688 / 7686) * (7688 / 7686)) * ((992 / 990) * (1984 / 1982))) := by
  classical
  have hzpow : ∀ k : ℕ, ¬ 31 ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 31) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 31).dvd_of_dvd_pow h)
    omega
  have hmem : ∀ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61),
      x ∈ L ∧ 31 ∣ x + 1 ∧ ¬ x = 61 := fun x hx =>
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2, (Finset.mem_filter.mp hx).2⟩
  have hform : ∀ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * 31 ^ j := by
    intro x hx
    obtain ⟨hxL, hxz, -⟩ := hmem x hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := 31) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have hzo : Odd (31 ^ j) := Odd.pow (by decide)
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at hzo
      rcases hodd with ⟨u, hu⟩
      rcases hzo with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hxz
      exact hzpow k hxz
  have hB0 : ∀ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61),
      (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x (hmem x hx).1).1.one_lt.le
  -- j ≥ 3
  have hA : ∏ x ∈ ((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61)).filter
      (fun x => 29791 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ 29791 / 29788 := by
    have h := zleaf_bound (z := 31) (by norm_num) 3 (by norm_num)
      (((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61)).filter
        (fun x => 29791 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx1, hcu⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, j, hk, ?_, hkj⟩
        by_contra hj3
        have hj' : j = 1 ∨ j = 2 := by omega
        rcases hj' with rfl | rfl
        · rw [hkj, pow_one, show (29791 : ℕ) = 961 * 31 by norm_num] at hcu
          exact hzpow k ((by norm_num : (31 : ℕ) ∣ 961).trans
            (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hcu))
        · rw [hkj, show (29791 : ℕ) = 31 * 31 ^ 2 by norm_num] at hcu
          exact hzpow k (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hcu))
    norm_num at h ⊢
    exact h
  -- j = 2
  have hB2 : ∏ x ∈ (((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61)).filter
      (fun x => ¬ 29791 ∣ x + 1)).filter (fun x => 961 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (7688 / 7686) * (7688 / 7686) := by
    have h := fiber_split (u0 := 961) (k0 := 3) (q0 := 7687) (by norm_num) (by norm_num)
      ((((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61)).filter
        (fun x => ¬ 29791 ∣ x + 1)).filter (fun x => 961 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx2, hsq⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx1, hcu⟩ := Finset.mem_filter.mp hx2
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, hk, ?_⟩
        have hj2 : j = 2 := by
          by_contra hne
          have hj' : j = 1 ∨ 3 ≤ j := by omega
          rcases hj' with rfl | hj3
          · rw [hkj, pow_one, show (961 : ℕ) = 31 * 31 by norm_num] at hsq
            exact hzpow k (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hsq)
          · apply hcu
            rw [hkj, show (29791 : ℕ) = 31 ^ 3 by norm_num]
            exact Dvd.dvd.mul_left (pow_dvd_pow 31 hj3) _
        rw [hkj, hj2]
        norm_num) (fun x hx k hk hk3 hkx => by
        have hxp := (hLp x (hmem x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1).1
        interval_cases k <;> norm_num at hkx <;>
          first
          | omega
          | (have hx' : x = 1921 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 3843 := by omega
             subst hx'; exact absurd hxp (by norm_num)))
    norm_num at h ⊢
    exact h
  -- j = 1
  have hB1 : ∏ x ∈ (((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61)).filter
      (fun x => ¬ 29791 ∣ x + 1)).filter (fun x => ¬ 961 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (992 / 990) * (1984 / 1982) := by
    have h := fiber_split (u0 := 31) (k0 := 6) (q0 := 991) (by norm_num) (by norm_num)
      ((((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61)).filter
        (fun x => ¬ 29791 ∣ x + 1)).filter (fun x => ¬ 961 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx2, hsq⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx2
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, hk, ?_⟩
        have hj1 : j = 1 := by
          by_contra hne
          apply hsq
          rw [hkj, show (961 : ℕ) = 31 ^ 2 by norm_num]
          exact Dvd.dvd.mul_left (pow_dvd_pow 31 (by omega)) _
        rw [hkj, hj1, pow_one]) (fun x hx k hk hk5 hkx => by
        have hx1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
        have hxp := (hLp x (hmem x hx1).1).1
        have hxe := (hmem x hx1).2.2
        have hxL := (hmem x hx1).1
        interval_cases k <;> norm_num at hkx <;>
          first
          | omega
          | (have hx' : x = 123 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 247 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 495 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 1983 := by omega
             subst hx'; exact absurd hxp (by norm_num)))
    norm_num at h ⊢
    exact h
  rw [← Finset.prod_filter_mul_prod_filter_not
    ((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61)) (fun x => 29791 ∣ x + 1)]
  refine mul_le_mul hA ?_ (Finset.prod_nonneg fun x hx => hB0 x (Finset.mem_filter.mp hx).1)
    (by norm_num)
  rw [← Finset.prod_filter_mul_prod_filter_not
    (((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61)).filter
      (fun x => ¬ 29791 ∣ x + 1)) (fun x => 961 ∣ x + 1)]
  exact mul_le_mul hB2 hB1 (Finset.prod_nonneg fun x hx =>
    hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1) (by norm_num)

/-- Core prime `31`, `61` not a leaf: the leaves `x ≠ 991` with `x + 1 = 2 ^ k * 31 ^ j`, `j ≥ 1`: for `j = 1` only
`3967` has `k ≤ 8` (`123, 247, 495, 1983, 7935` are not prime), for `j = 2` only `7687` has `k ≤ 3`. -/
theorem thirtyone_leaves_a {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 31) (h61 : 61 ∉ L) :
    ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      (29791 / 29788) * (((7688 / 7686) * (7688 / 7686)) * ((3968 / 3966) * (7936 / 7934))) := by
  classical
  have hzpow : ∀ k : ℕ, ¬ 31 ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 31) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 31).dvd_of_dvd_pow h)
    omega
  have hmem : ∀ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
      x ∈ L ∧ 31 ∣ x + 1 ∧ ¬ x = 991 := fun x hx =>
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2, (Finset.mem_filter.mp hx).2⟩
  have hform : ∀ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * 31 ^ j := by
    intro x hx
    obtain ⟨hxL, hxz, -⟩ := hmem x hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := 31) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have hzo : Odd (31 ^ j) := Odd.pow (by decide)
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at hzo
      rcases hodd with ⟨u, hu⟩
      rcases hzo with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hxz
      exact hzpow k hxz
  have hB0 : ∀ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
      (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x (hmem x hx).1).1.one_lt.le
  -- j ≥ 3
  have hA : ∏ x ∈ ((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991)).filter
      (fun x => 29791 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ 29791 / 29788 := by
    have h := zleaf_bound (z := 31) (by norm_num) 3 (by norm_num)
      (((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991)).filter
        (fun x => 29791 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx1, hcu⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, j, hk, ?_, hkj⟩
        by_contra hj3
        have hj' : j = 1 ∨ j = 2 := by omega
        rcases hj' with rfl | rfl
        · rw [hkj, pow_one, show (29791 : ℕ) = 961 * 31 by norm_num] at hcu
          exact hzpow k ((by norm_num : (31 : ℕ) ∣ 961).trans
            (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hcu))
        · rw [hkj, show (29791 : ℕ) = 31 * 31 ^ 2 by norm_num] at hcu
          exact hzpow k (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hcu))
    norm_num at h ⊢
    exact h
  -- j = 2
  have hB2 : ∏ x ∈ (((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991)).filter
      (fun x => ¬ 29791 ∣ x + 1)).filter (fun x => 961 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (7688 / 7686) * (7688 / 7686) := by
    have h := fiber_split (u0 := 961) (k0 := 3) (q0 := 7687) (by norm_num) (by norm_num)
      ((((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991)).filter
        (fun x => ¬ 29791 ∣ x + 1)).filter (fun x => 961 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx2, hsq⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx1, hcu⟩ := Finset.mem_filter.mp hx2
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, hk, ?_⟩
        have hj2 : j = 2 := by
          by_contra hne
          have hj' : j = 1 ∨ 3 ≤ j := by omega
          rcases hj' with rfl | hj3
          · rw [hkj, pow_one, show (961 : ℕ) = 31 * 31 by norm_num] at hsq
            exact hzpow k (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hsq)
          · apply hcu
            rw [hkj, show (29791 : ℕ) = 31 ^ 3 by norm_num]
            exact Dvd.dvd.mul_left (pow_dvd_pow 31 hj3) _
        rw [hkj, hj2]
        norm_num) (fun x hx k hk hk3 hkx => by
        have hxp := (hLp x (hmem x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1).1
        interval_cases k <;> norm_num at hkx <;>
          first
          | omega
          | (have hx' : x = 1921 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 3843 := by omega
             subst hx'; exact absurd hxp (by norm_num)))
    norm_num at h ⊢
    exact h
  -- j = 1
  have hB1 : ∏ x ∈ (((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991)).filter
      (fun x => ¬ 29791 ∣ x + 1)).filter (fun x => ¬ 961 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (3968 / 3966) * (7936 / 7934) := by
    have h := fiber_split (u0 := 31) (k0 := 8) (q0 := 3967) (by norm_num) (by norm_num)
      ((((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991)).filter
        (fun x => ¬ 29791 ∣ x + 1)).filter (fun x => ¬ 961 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx2, hsq⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx2
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, hk, ?_⟩
        have hj1 : j = 1 := by
          by_contra hne
          apply hsq
          rw [hkj, show (961 : ℕ) = 31 ^ 2 by norm_num]
          exact Dvd.dvd.mul_left (pow_dvd_pow 31 (by omega)) _
        rw [hkj, hj1, pow_one]) (fun x hx k hk hk5 hkx => by
        have hx1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
        have hxp := (hLp x (hmem x hx1).1).1
        have hxe := (hmem x hx1).2.2
        have hxL := (hmem x hx1).1
        interval_cases k <;> norm_num at hkx <;>
          first
          | omega
          | (have hx' : x = 61 := by omega
             subst hx'; exact absurd hxL h61)
          | (have hx' : x = 123 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 247 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 495 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 1983 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 7935 := by omega
             subst hx'; exact absurd hxp (by norm_num)))
    norm_num at h ⊢
    exact h
  rw [← Finset.prod_filter_mul_prod_filter_not
    ((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991)) (fun x => 29791 ∣ x + 1)]
  refine mul_le_mul hA ?_ (Finset.prod_nonneg fun x hx => hB0 x (Finset.mem_filter.mp hx).1)
    (by norm_num)
  rw [← Finset.prod_filter_mul_prod_filter_not
    (((L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991)).filter
      (fun x => ¬ 29791 ∣ x + 1)) (fun x => 961 ∣ x + 1)]
  exact mul_le_mul hB2 hB1 (Finset.prod_nonneg fun x hx =>
    hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1) (by norm_num)

/-- A prime `p` with `991 ∣ p + 1` is at least `7927` (`1981`, `3963`, `5945` are not prime). -/
theorem nx991 {p : ℕ} (hp : p.Prime) (hd : 991 ∣ p + 1) : 7927 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 991 * k - 1 := by omega
  interval_cases k <;> first | omega | (norm_num at hp)

/-- `3, 5, 7, 13, 61` cannot all be simple primes: `(4/3)(6/5)(8/7)(14/13)(62/61) > 2`. -/
theorem kill_7_13_61 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (h3 : 3 ∈ P) (h5 : 5 ∈ P) (h7 : 7 ∈ P) (h13 : 13 ∈ P) (h61 : 61 ∈ P) : False := by
  refine lower_kill hP hz E (S := {3, 5, 7, 13, 61}) ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num

/-- Splits one element `q` off a product of default weights. -/
theorem split_leaf (S : Finset ℕ) (q : ℕ) (hq : 2 ≤ q) (hS : ∀ x ∈ S, 1 ≤ x) :
    ∏ x ∈ S, (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) *
        ∏ x ∈ S.filter (fun x => ¬ x = q), (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
  classical
  have h1 : ∏ x ∈ S.filter (fun x => x = q), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((q : ℚ) + 1) / ((q : ℚ) - 1) := by
    have hsub : S.filter (fun x => x = q) ⊆ ({q} : Finset ℕ) := fun x hx => by
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hx).2
    have h := Finset.prod_le_prod_of_subset_of_one_le
      (f := fun x : ℕ => ((x : ℚ) + 1) / ((x : ℚ) - 1)) hsub
      (fun x hx => B_nonneg (hS x (Finset.mem_filter.mp hx).1)) (fun x hx _ => by
        rw [Finset.mem_singleton.mp hx]
        show (1 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1)
        have h2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
        rw [le_div_iff₀ (by linarith)]
        linarith)
    rwa [Finset.prod_singleton] at h
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun x => x = q)]
  exact mul_le_mul_of_nonneg_right h1
    (Finset.prod_nonneg fun x hx => B_nonneg (hS x (Finset.mem_filter.mp hx).1))

/-- The weights argument for the core prime `31` and `a = 2 (mod 4)` when `13` and `103` are simple primes
and `127` is not: `3` weighs `8/5`, the chain `7 ← 13 ← 103` ends with kept parents of `103` at least `823`,
and the leaf `991` (`992 = 32 * 31`) weighs `(992/991)(7928/7926)` because its parents are at least `7927`. -/
theorem thirtyone_master_a {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 31 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 31 ^ e * ∏ p ∈ P, p)
    (hzP : 31 ∉ P) (h5P : 5 ∈ P) (h5c : ∀ p ∈ P, ¬ 5 ∣ p + 1) (h13 : 13 ∈ P) (h103 : 103 ∈ P)
    (h127 : 127 ∉ P) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 31) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + 31 ^ e : ℕ) : ℚ) / ((31 ^ e : ℕ) : ℚ)) *
        ((8 / 5 * (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) * 1 * 1 * (2048 / 2047)) *
          ((992 / 991 * (7928 / 7926)) *
            ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
              (((x : ℚ) + 1) / ((x : ℚ) - 1)))) := by
  classical
  have hz : Nat.Prime 31 := by norm_num
  have hK : ∀ c : ℕ, c.Prime → c ∣ 31 ^ e → c ∈ ({31} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, F3, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨β, hβ3, hβ5, hβ7, hβ13, hβ31, hβ103, hβ127, hβ991, hβ⟩ : ∃ β : ℕ → ℚ, β 3 = 8 / 5 ∧
      β 5 = 6 / 5 ∧ β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) ∧
      β 13 = 14 / 13 * (104 / 103 * (824 / 822)) ∧ β 31 = 1 ∧ β 103 = 104 / 103 * (824 / 822) ∧
      β 127 = 1 ∧ β 991 = 992 / 991 * (7928 / 7926) ∧
      ∀ x : ℕ, x ≠ 3 → x ≠ 5 → x ≠ 7 → x ≠ 13 → x ≠ 31 → x ≠ 103 → x ≠ 127 → x ≠ 991 →
        β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = 3 then 8 / 5 else if x = 5 then 6 / 5
      else if x = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))
      else if x = 13 then 14 / 13 * (104 / 103 * (824 / 822)) else if x = 31 then 1
      else if x = 103 then 104 / 103 * (824 / 822) else if x = 127 then 1
      else if x = 991 then 992 / 991 * (7928 / 7926) else ((x : ℚ) + 1) / ((x : ℚ) - 1),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      fun x h1 h2 h3 h4 h5 h6 h7 h8 => by simp [h1, h2, h3, h4, h5, h6, h7, h8]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [hβ3]
      norm_num
    by_cases e5 : p = 5
    · subst e5
      rw [hβ5]
      norm_num
    by_cases e7 : p = 7
    · subst e7
      rw [hβ7]
      norm_num
    by_cases e13 : p = 13
    · subst e13
      rw [hβ13]
      norm_num
    by_cases e31 : p = 31
    · subst e31
      exact absurd hp hzP
    by_cases e103 : p = 103
    · subst e103
      rw [hβ103]
      norm_num
    by_cases e127 : p = 127
    · subst e127
      exact absurd hp h127
    by_cases e991 : p = 991
    · subst e991
      rw [hβ991]
      norm_num
    rw [hβ p e3 e5 e7 e13 e31 e103 e127 e991]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) →
      c = 3 ∨ c = 5 ∨ c = 7 ∨ c = 13 ∨ c = 31 ∨ c = 103 ∨ c = 127 ∨ c = 991 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (hβ c hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2.1 hcon.2.2.2.2.1 hcon.2.2.2.2.2.1
      hcon.2.2.2.2.2.2.1 hcon.2.2.2.2.2.2.2)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({31} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne
    have hpp := (hP p hp).1
    have hwp := (hBd p hp).2
    rcases hsp c hne with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hp5 : p = 5 := F3 3 Nat.prime_three (by norm_num) (by simp) p hp 5 h5P hd (by norm_num)
      rw [hp5, hβ5, hβ3]
      norm_num
    · exact absurd hd (h5c p hp)
    · have hp13 : p = 13 := F3 7 (by norm_num) (by norm_num) (by simp) p hp 13 h13 hd (by norm_num)
      rw [hp13, hβ13, hβ7]
      norm_num
    · have hp103 : p = 103 :=
        F3 13 (by norm_num) (by norm_num) (by simp) p hp 103 h103 hd (by norm_num)
      rw [hp103, hβ103, hβ13]
      norm_num
    · exact absurd hc hzP
    · rw [hβ103]
      exact far_step (c := 103) (N := 823) (by norm_num)
        (nx103 (z := 31) (by norm_num) hpp hd hl) hwp (le_of_eq (by norm_num))
    · exact absurd hc h127
    · rw [hβ991]
      exact far_step (c := 991) (N := 7927) (by norm_num) (nx991 hpp hd) hwp
        (le_of_eq (by norm_num))
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 31 := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hM : ∏ x ∈ L.filter (fun x => ¬ 31 ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hβ31, hβ127]
      norm_num
  rw [hβ3, hβ7, hβ31, hβ127] at hM
  have h991 : ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => x = 991), β x ≤
      992 / 991 * (7928 / 7926) := by
    have hsub : (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => x = 991) ⊆
        ({991} : Finset ℕ) := fun x hx => by
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hx).2
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx _ => by
        rw [Finset.mem_singleton.mp hx, hβ991]
        norm_num)
    rwa [Finset.prod_singleton, hβ991] at h
  have hrest : ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991), β x ≤
      ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
  have hZ : ∏ x ∈ L.filter (fun x => 31 ∣ x + 1), β x ≤ (992 / 991 * (7928 / 7926)) *
      ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => 31 ∣ x + 1))
      (fun x => x = 991) β]
    exact mul_le_mul h991 hrest (Finset.prod_nonneg fun x hx =>
      (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le) (by norm_num)
  have hX : ∏ x ∈ L, β x ≤
      (8 / 5 * (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) * 1 * 1 * (2048 / 2047)) *
        ((992 / 991 * (7928 / 7926)) *
          ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
            (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => 31 ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by norm_num)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- `z = 31`, `a = 2 (mod 4)`, `a ≥ 22`, `e ≥ 3`: no solution. Cases on which of `13, 61, 103, 127` are simple
primes; totals at most `1.99950`. -/
theorem amod4_31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 31 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 31 ^ e * ∏ p ∈ P, p)
    (hzP : 31 ∉ P) (hm4 : m % 4 = 2) (hm : 22 ≤ m) (he : 3 ≤ e) : False := by
  classical
  have hz : Nat.Prime 31 := by norm_num
  obtain ⟨h3P, h5P, h5c, -⟩ := setup5 hP hz (by norm_num) E hm4
  have hK : ∀ c : ℕ, c.Prime → c ∣ 31 ^ e → c ∈ ({31} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨F1, -, -, -, -, -, -, -⟩ := facts hP hK E
  by_cases h13 : 13 ∈ P
  · have h7 : 7 ∈ P := F1 7 (by norm_num) (by norm_num) (by simp) 13 h13 (by norm_num)
    by_cases h61 : 61 ∈ P
    · exact kill_7_13_61 hP hz E h3P h5P h7 h13 h61
    · by_cases h103 : 103 ∈ P
      · by_cases h127 : 127 ∈ P
        · exact kill_7_13_103_127 hP hz E h3P h5P h7 h13 h103 h127
        · -- 7 <- 13 <- 103; 61 and 127 are not simple; the leaf 991 has its own weight
          obtain ⟨L, hLP, hleaf, hmain⟩ := thirtyone_master_a hP E hzP h5P h5c h13 h103 h127
          have h61L : 61 ∉ L := fun h => h61 (hLP h)
          have hZ := thirtyone_leaves_a (fun x hx => hP x (hLP hx)) hleaf h61L
          have hZ0 : (0 : ℚ) ≤ ∏ x ∈ (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 991),
              (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
            Finset.prod_nonneg fun x hx => B_nonneg
              (hP x (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)).1.one_lt.le
          refine table_close hm hmain (by positivity)
            (kk_le (a := 31) (b := 3) (by norm_num) (le_refl _) he) (by norm_num)
            (mul_nonneg (by norm_num) hZ0) (mul_le_mul_of_nonneg_left hZ (by norm_num)) ?_
          norm_num
      · -- 7 <- 13, kept parents of 13 at least 883; 61 and 103 are not simple
        obtain ⟨L, hLP, hleaf, hmain⟩ := table_master hP hz (by norm_num) E hzP h5P h5c
          (8 / 7 * (14 / 13 * (884 / 882))) (14 / 13 * (884 / 882)) 1
          1 1 (128 / 127 * (4064 / 4062))
          ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
          ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h103, le_refl _⟩))⟩⟩
          ⟨le_refl _, fun h => absurd h hzP⟩
          ⟨le_refl _, fun h => absurd h h61⟩
          ⟨le_refl _, fun h => absurd h h103⟩
          ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
        have hZ := thirtyone_leaves (fun x hx => hP x (hLP hx)) hleaf
        have heq : (L.filter (fun x => 31 ∣ x + 1)).filter (fun x => ¬ x = 61) =
            L.filter (fun x => 31 ∣ x + 1) :=
          Finset.filter_true_of_mem (fun x hx => by
            rintro rfl
            exact h61 (hLP (Finset.mem_filter.mp hx).1))
        rw [heq] at hZ
        refine table_close hm hmain (by positivity)
          (kk_le (a := 31) (b := 3) (by norm_num) (le_refl _) he) (by norm_num)
          (Finset.prod_nonneg fun x hx =>
            B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) hZ ?_
        norm_num
  · -- 13 is not simple: kept parents of 7 at least 181; the leaf 61 keeps the default weight 62/60
    obtain ⟨L, hLP, hleaf, hmain⟩ := table_master hP hz (by norm_num) E hzP h5P h5c
      (8 / 7 * (182 / 180)) 1 1
      (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
      ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h13, le_refl _⟩))⟩⟩
      ⟨le_refl _, fun h => absurd h h13⟩
      ⟨le_refl _, fun h => absurd h hzP⟩
      ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
      ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
      ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
    have hZ := thirtyone_leaves (fun x hx => hP x (hLP hx)) hleaf
    have hS := split_leaf (L.filter (fun x => 31 ∣ x + 1)) 61 (by norm_num)
      (fun x hx => (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le)
    refine table_close hm hmain (by positivity)
      (kk_le (a := 31) (b := 3) (by norm_num) (le_refl _) he) (by norm_num)
      (Finset.prod_nonneg fun x hx =>
        B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le)
      (hS.trans (mul_le_mul_of_nonneg_left hZ (by norm_num))) ?_
    norm_num

/-- The weights argument for `a` odd: `3 ∣ 2 ^ a + 1` is the source of `3`, so `3` has no consumer and weighs
`4/3`; default weights elsewhere. -/
theorem odd_master {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz5 : 5 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hmo : m % 2 = 1) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ((4 / 3 * (4 / 3) * (16 / 15) * (64 / 63) * (2048 / 2047)) *
          ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, -, F4, -, -, -, -⟩ := facts hP hK E
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have hno3 : ∀ p ∈ P, ¬ 3 ∣ p + 1 :=
    F4 3 Nat.prime_three (by norm_num) h3z (three_dvd_two_pow_add_one hmo)
  obtain ⟨β, hβ3, hβ⟩ : ∃ β : ℕ → ℚ, β 3 = 4 / 3 ∧
      ∀ x : ℕ, x ≠ 3 → β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = 3 then 4 / 3 else ((x : ℚ) + 1) / ((x : ℚ) - 1), by simp,
      fun x h1 => by simp [h1]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [hβ3]
      norm_num
    rw [hβ p e3]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne
    by_cases e3 : c = 3
    · subst e3
      exact absurd hd (hno3 p hp)
    · exact absurd (hβ c e3) hne
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hd7 := hβ 7 (by norm_num)
  have hd31 := hβ 31 (by norm_num)
  have hd127 := hβ 127 (by norm_num)
  have e7 : (((7 : ℕ) : ℚ) + 1) / (((7 : ℕ) : ℚ) - 1) = 4 / 3 := by norm_num
  have e31 : (((31 : ℕ) : ℚ) + 1) / (((31 : ℕ) : ℚ) - 1) = 16 / 15 := by norm_num
  have e127 : (((127 : ℕ) : ℚ) + 1) / (((127 : ℕ) : ℚ) - 1) = 64 / 63 := by norm_num
  rw [e7] at hd7
  rw [e31] at hd31
  rw [e127] at hd127
  have hM : ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hd7, hd31, hd127]
      norm_num
  rw [hβ3, hd7, hd31, hd127] at hM
  have hZ : ∏ x ∈ L.filter (fun x => z ∣ x + 1), β x ≤
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod (fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp hx).1)
  have hX : ∏ x ∈ L, β x ≤ (4 / 3 * (4 / 3) * (16 / 15) * (64 / 63) * (2048 / 2047)) *
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => z ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by norm_num)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- `z ≥ 61` and `a` odd: `a ≤ 7`. Total at most `1.99872` for `a ≥ 9`. -/
theorem odd_bound61 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz61 : 61 ≤ z)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) (c : padicValNat 2 n % 2 = 1) :
    padicValNat 2 n ≤ 7 := by
  by_contra hgt
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS z).mpr rfl).2.2
  exact table_finish hP hz (by norm_num) hz61 (by omega : 9 ≤ padicValNat 2 n) he2 (by norm_num)
    (odd_master hP hz (by omega) E c) (by norm_num)

/-- `61 ≤ z < 4097`, `4 ∣ a` and the exact power of `2` in `a` at least `2 ^ 11`: no solution. The Fermat
prime `c ≥ 4097` is not `z`, so it is the simple prime with `3 ∣ c + 1`. -/
theorem four_dvd_dead61 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz61 : 61 ≤ z)
    (hz4097 : z < 4097) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (h4 : padicValNat 2 n % 4 = 0)
    (h8 : padicValNat 2 n % 8 ≠ 4) (h16 : padicValNat 2 n % 16 ≠ 8) (h32 : padicValNat 2 n % 32 ≠ 16) (h64 : padicValNat 2 n % 64 ≠ 32)
    (h128 : padicValNat 2 n % 128 ≠ 64) (h256 : padicValNat 2 n % 256 ≠ 128) (h512 : padicValNat 2 n % 512 ≠ 256)
    (h1024 : padicValNat 2 n % 1024 ≠ 512) (h2048 : padicValNat 2 n % 2048 ≠ 1024) :
    padicValNat 2 n = 0 := by
  classical
  by_contra hm0
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS z).mpr rfl).2.2
  have hme : Even (padicValNat 2 n) := Nat.even_iff.mpr (by omega)
  obtain ⟨c, k, t, hc, hc2, hc3, hcm, hk, hcF, ht, hmt⟩ := exists_fermat_prime hm0 hme
  have hk11 : 11 ≤ k := v2_large ht hmt h4 h8 h16 h32 h64 h128 h256 h512 h1024 h2048
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ n.factorization z → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, F2, -, -, -, -, -, -⟩ := facts hP hK E
  have hd := two_pow_succ_dvd_pred hc hcF
  have hc4097 : 4097 ≤ c := by
    have h12 : 2 ^ 12 ∣ c - 1 := (pow_dvd_pow 2 (by omega : 12 ≤ k + 1)).trans hd
    have hc2' := hc.two_le
    have hle := Nat.le_of_dvd (by omega) h12
    norm_num at hle
    omega
  have hcz : c ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have hcP := F2 c hc hc2 hcz hcm
  have h3c : 3 ∣ c + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hm11 : 11 ≤ padicValNat 2 n := by
    have h1 : 2048 ≤ 2 ^ k := by
      calc 2048 = 2 ^ 11 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk11
    have ht1 : 1 ≤ t := by
      obtain ⟨s, rfl⟩ := ht
      omega
    have h2 : 2 ^ k * 1 ≤ 2 ^ k * t := Nat.mul_le_mul_left _ ht1
    omega
  exact pinned_generic hP hz hz61 E hcP h3c hc4097 hm11 he2

/-- `z ≥ 823`, `8 ∣ e`, `a = 2 (mod 4)`: `a ≤ 21`. -/
theorem amod4_dead823 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz823 : 823 ≤ z)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) (he : n.factorization z % 8 = 0)
    (h4 : padicValNat 2 n % 4 = 2) : padicValNat 2 n ≤ 21 := by
  by_contra hgt
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS z).mpr rfl).2.2
  have hzP : z ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)) := fun hmem =>
    (Finset.mem_filter.mp hmem).2 (Finset.mem_singleton_self z)
  exact amod4_large hP hz hz823 E hzP h4 (by omega) (by omega)

/-- `a = 2 (mod 4)`, `a ≥ 22`, `e ≥ 3`, `z ≥ 17`: no solution as soon as the leaves bound of `zleaves_skip`
(no prime `2 ^ k * z - 1` with `k ≤ s`) brings the worst of the three totals of `amod4_large` below `2`. -/
theorem amod4_skip {m e z s : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz17 : 17 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hzP : z ∉ P) (hs : ∀ k : ℕ, 1 ≤ k → k ≤ s → ¬ (2 ^ k * z - 1).Prime)
    (hm4 : m % 4 = 2) (hm : 22 ≤ m) (he : 3 ≤ e)
    (hnum : (1 + 1 / (2 : ℚ) ^ 22) * (((1 + z ^ 3 : ℕ) : ℚ) / ((z ^ 3 : ℕ) : ℚ)) *
      ((8 / 5 * (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) * 1 * 1 * (2048 / 2047)) *
        (((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)))) < 2) :
    False := by
  classical
  obtain ⟨h3P, h5P, h5c, -⟩ := setup5 hP hz (by omega) E hm4
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨F1, -, -, -, -, -, -, -⟩ := facts hP hK E
  have h7z : (7 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have hzq : (17 : ℚ) ≤ (z : ℚ) := by exact_mod_cast hz17
  have hu : (17 : ℚ) ≤ ((2 ^ s * z : ℕ) : ℚ) := by
    have h1 : z ≤ 2 ^ s * z := Nat.le_mul_of_pos_left z (pow_pos (by norm_num) s)
    exact_mod_cast hz17.trans h1
  have hZL0 : (0 : ℚ) ≤ ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) *
      (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)) :=
    mul_nonneg (div_nonneg (by positivity) (by nlinarith)) (div_nonneg (by linarith) (by linarith))
  have hfac0 : (0 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ 22) * (((1 + z ^ 3 : ℕ) : ℚ) / ((z ^ 3 : ℕ) : ℚ)) := by
    positivity
  have hsmaller : ∀ C : ℚ,
      C ≤ 8 / 5 * (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) * 1 * 1 * (2048 / 2047) →
      (1 + 1 / (2 : ℚ) ^ 22) * (((1 + z ^ 3 : ℕ) : ℚ) / ((z ^ 3 : ℕ) : ℚ)) *
        (C * (((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)))) < 2 := fun C hC =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC hZL0) hfac0) hnum
  by_cases h13 : 13 ∈ P
  · have h7 : 7 ∈ P := F1 7 (by norm_num) (by norm_num) h7z 13 h13 (by norm_num)
    by_cases h31 : 31 ∈ P
    · exact kill_7_13_31 hP hz E h3P h5P h7 h13 h31
    · by_cases h103 : 103 ∈ P
      · by_cases h127 : 127 ∈ P
        · exact kill_7_13_103_127 hP hz E h3P h5P h7 h13 h103 h127
        · -- 7 <- 13 <- 103, kept parents of 103 at least 823; 31 and 127 are not simple
          exact table_finish_skip hP hz (by omega) hs hm he (by norm_num)
            (table_master hP hz hz17 E hzP h5P h5c
              (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) (14 / 13 * (104 / 103 * (824 / 822))) 1
              (31 / 30) (104 / 103 * (824 / 822)) 1
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h103, le_refl _⟩))⟩⟩
              ⟨le_refl _, fun h => absurd h h31⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
              ⟨le_refl _, fun h => absurd h h127⟩)
            hnum
      · -- 7 <- 13, kept parents of 13 at least 883; 31 is not simple
        exact table_finish_skip hP hz (by omega) hs hm he (by norm_num)
          (table_master hP hz hz17 E hzP h5P h5c
            (8 / 7 * (14 / 13 * (884 / 882))) (14 / 13 * (884 / 882)) 1
            (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h103, le_refl _⟩))⟩⟩
            ⟨le_refl _, fun h => absurd h h31⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩)
          (hsmaller _ (by norm_num))
  · -- 13 is not simple: kept parents of 7 at least 181
    exact table_finish_skip hP hz (by omega) hs hm he (by norm_num)
      (table_master hP hz hz17 E hzP h5P h5c
        (8 / 7 * (182 / 180)) 1 (16 / 15)
        (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h13, le_refl _⟩))⟩⟩
        ⟨le_refl _, fun h => absurd h h13⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩)
      (hsmaller _ (by norm_num))

/-- If `q0` is the only prime `2 ^ k * z - 1` with `1 ≤ k ≤ s`, the leaves `x` with `x + 1 = 2 ^ k * z ^ j`,
`j ≥ 1`, weigh at most `z^2/(z^2-3) * ((q0+1)/(q0-1) * u/(u-2))` with `u = 2 ^ s * z`. -/
theorem zleaves_one {z s q0 : ℕ} (hz : z.Prime) (hz5 : 5 ≤ z) (hq0 : 2 ≤ q0)
    (hs : ∀ k : ℕ, 1 ≤ k → k ≤ s → (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 = q0) {L : Finset ℕ}
    (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) :
    ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) *
        ((((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2))) := by
  classical
  have hzpow : ∀ k : ℕ, ¬ z ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow h)
    omega
  have hform : ∀ x ∈ L.filter (fun x => z ∣ x + 1),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * z ^ j := by
    intro x hx
    obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := z) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have hzo : Odd (z ^ j) := Odd.pow (hz.odd_of_ne_two (by omega))
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at hzo
      rcases hodd with ⟨u, hu⟩
      rcases hzo with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hxz
      exact hzpow k hxz
  have hB0 : ∀ x ∈ L, (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x hx).1.one_lt.le
  have hA : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => z ^ 2 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) :=
    zleaf_bound (z := z) (by omega) 2 (by norm_num) _ (fun x hx => by
      obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
      obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
      refine ⟨k, j, hk, ?_, hkj⟩
      by_contra hj2
      have hj1 : j = 1 := by omega
      subst hj1
      rw [hkj, pow_one, pow_two] at hzz
      exact hzpow k (Nat.dvd_of_mul_dvd_mul_right hz.pos hzz))
  have hj1 : ∀ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ z ^ 2 ∣ x + 1),
      ∃ k, 1 ≤ k ∧ x + 1 = 2 ^ k * z := by
    intro x hx
    obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
    refine ⟨k, hk, ?_⟩
    have hj1 : j = 1 := by
      by_contra hne
      apply hzz
      rw [hkj]
      exact Dvd.dvd.mul_left (pow_dvd_pow z (by omega)) _
    rw [hkj, hj1, pow_one]
  have hB' : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ z ^ 2 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
        (((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)) :=
    fiber_split (u0 := z) (k0 := s) (q0 := q0) (by omega) hq0 _ hj1 (fun x hx k hk hks hkx => by
      have hxL : x ∈ L := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
      have hx' : x = 2 ^ k * z - 1 := by omega
      rw [hx']
      exact hs k hk hks (hx' ▸ (hLp x hxL).1))
  rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => z ∣ x + 1))
    (fun x => z ^ 2 ∣ x + 1)]
  refine mul_le_mul hA hB' (Finset.prod_nonneg fun x hx => ?_) ?_
  · exact hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  · have h5 : (5 : ℚ) ≤ z := by exact_mod_cast hz5
    exact div_nonneg (by positivity) (by nlinarith)

/-- `a = 2 (mod 4)`, `a ≥ 22`, `e ≥ 3`, `z ≥ 17`: no solution as soon as the leaves `x` with `z ∣ x + 1` weigh
at most `Zb` and the worst of the three totals of `amod4_large` is below `2` with this bound. -/
theorem amod4_leaf {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz17 : 17 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hzP : z ∉ P) (hm4 : m % 4 = 2) (hm : 22 ≤ m) (he : 3 ≤ e) (Zb : ℚ) (hZb0 : 0 ≤ Zb)
    (hZ : ∀ L : Finset ℕ, L ⊆ P → (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) →
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ Zb)
    (hnum : (1 + 1 / (2 : ℚ) ^ 22) * (((1 + z ^ 3 : ℕ) : ℚ) / ((z ^ 3 : ℕ) : ℚ)) *
      ((8 / 5 * (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) * 1 * 1 * (2048 / 2047)) * Zb) < 2) :
    False := by
  classical
  obtain ⟨h3P, h5P, h5c, -⟩ := setup5 hP hz (by omega) E hm4
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨F1, -, -, -, -, -, -, -⟩ := facts hP hK E
  have h7z : (7 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have hfac0 : (0 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ 22) * (((1 + z ^ 3 : ℕ) : ℚ) / ((z ^ 3 : ℕ) : ℚ)) := by
    positivity
  have hfin : ∀ C : ℚ, 0 ≤ C →
      C ≤ 8 / 5 * (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) * 1 * 1 * (2048 / 2047) →
      (∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
        (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
          (C * ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)))) → False := by
    rintro C hC0 hC ⟨L, hLP, hleaf, hmain⟩
    exact table_close hm hmain (by positivity) (kk_le (by omega) (le_refl z) he) hC0
      (Finset.prod_nonneg fun x hx =>
        B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) (hZ L hLP hleaf)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC hZb0) hfac0) hnum)
  by_cases h13 : 13 ∈ P
  · have h7 : 7 ∈ P := F1 7 (by norm_num) (by norm_num) h7z 13 h13 (by norm_num)
    by_cases h31 : 31 ∈ P
    · exact kill_7_13_31 hP hz E h3P h5P h7 h13 h31
    · by_cases h103 : 103 ∈ P
      · by_cases h127 : 127 ∈ P
        · exact kill_7_13_103_127 hP hz E h3P h5P h7 h13 h103 h127
        · -- 7 <- 13 <- 103, kept parents of 103 at least 823; 31 and 127 are not simple
          exact hfin _ (by norm_num) (le_refl _)
            (table_master hP hz hz17 E hzP h5P h5c
              (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) (14 / 13 * (104 / 103 * (824 / 822))) 1
              (31 / 30) (104 / 103 * (824 / 822)) 1
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h103, le_refl _⟩))⟩⟩
              ⟨le_refl _, fun h => absurd h h31⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
              ⟨le_refl _, fun h => absurd h h127⟩)
      · -- 7 <- 13, kept parents of 13 at least 883; 31 is not simple
        exact hfin _ (by norm_num) (by norm_num)
          (table_master hP hz hz17 E hzP h5P h5c
            (8 / 7 * (14 / 13 * (884 / 882))) (14 / 13 * (884 / 882)) 1
            (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h103, le_refl _⟩))⟩⟩
            ⟨le_refl _, fun h => absurd h h31⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩)
  · -- 13 is not simple: kept parents of 7 at least 181
    exact hfin _ (by norm_num) (by norm_num)
      (table_master hP hz hz17 E hzP h5P h5c
        (8 / 7 * (182 / 180)) 1 (16 / 15)
        (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h13, le_refl _⟩))⟩⟩
        ⟨le_refl _, fun h => absurd h h13⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩)

/-- `zleaves_one` with two exceptional leaves: if `q0` and `q1` are the only primes `2 ^ k * z - 1` with
`1 ≤ k ≤ s`, the leaves `x` with `z ∣ x + 1` weigh at most
`z^2/(z^2-3) * ((q0+1)/(q0-1) * ((q1+1)/(q1-1) * u/(u-2)))` with `u = 2 ^ s * z`. -/
theorem zleaves_two {z s q0 q1 : ℕ} (hz : z.Prime) (hz5 : 5 ≤ z) (hq0 : 2 ≤ q0) (hq1 : 2 ≤ q1)
    (hs : ∀ k : ℕ, 1 ≤ k → k ≤ s → (2 ^ k * z - 1).Prime →
      2 ^ k * z - 1 = q0 ∨ 2 ^ k * z - 1 = q1) {L : Finset ℕ}
    (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) :
    ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) *
        ((((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) * ((((q1 : ℚ) + 1) / ((q1 : ℚ) - 1)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)))) := by
  classical
  have hzpow : ∀ k : ℕ, ¬ z ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow h)
    omega
  have hform : ∀ x ∈ L.filter (fun x => z ∣ x + 1),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * z ^ j := by
    intro x hx
    obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := z) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have hzo : Odd (z ^ j) := Odd.pow (hz.odd_of_ne_two (by omega))
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at hzo
      rcases hodd with ⟨u, hu⟩
      rcases hzo with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hxz
      exact hzpow k hxz
  have hB0 : ∀ x ∈ L, (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x hx).1.one_lt.le
  have hA : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => z ^ 2 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) :=
    zleaf_bound (z := z) (by omega) 2 (by norm_num) _ (fun x hx => by
      obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
      obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
      refine ⟨k, j, hk, ?_, hkj⟩
      by_contra hj2
      have hj1 : j = 1 := by omega
      subst hj1
      rw [hkj, pow_one, pow_two] at hzz
      exact hzpow k (Nat.dvd_of_mul_dvd_mul_right hz.pos hzz))
  have hj1 : ∀ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ z ^ 2 ∣ x + 1),
      ∃ k, 1 ≤ k ∧ x + 1 = 2 ^ k * z := by
    intro x hx
    obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
    refine ⟨k, hk, ?_⟩
    have hj1 : j = 1 := by
      by_contra hne
      apply hzz
      rw [hkj]
      exact Dvd.dvd.mul_left (pow_dvd_pow z (by omega)) _
    rw [hkj, hj1, pow_one]
  have hBq : ∀ q : ℕ, 2 ≤ q → (1 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
    have h2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
    rw [le_div_iff₀ (by linarith)]
    linarith
  have key : ∀ S : Finset ℕ, (∀ x ∈ S, x ∈ L) → (∀ x ∈ S, ∃ k, 1 ≤ k ∧ x + 1 = 2 ^ k * z) →
      ∏ x ∈ S, (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
        (((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) * ((((q1 : ℚ) + 1) / ((q1 : ℚ) - 1)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2))) := by
    intro S hSL hS1
    have h1 : ∏ x ∈ S.filter (fun x => x = q0), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
        ((q0 : ℚ) + 1) / ((q0 : ℚ) - 1) := by
      have hsub : S.filter (fun x => x = q0) ⊆ ({q0} : Finset ℕ) := fun x hx => by
        rw [Finset.mem_singleton]
        exact (Finset.mem_filter.mp hx).2
      have h := Finset.prod_le_prod_of_subset_of_one_le
        (f := fun x : ℕ => ((x : ℚ) + 1) / ((x : ℚ) - 1)) hsub
        (fun x hx => hB0 x (hSL x (Finset.mem_filter.mp hx).1)) (fun x hx _ => by
          rw [Finset.mem_singleton.mp hx]
          exact hBq q0 hq0)
      rwa [Finset.prod_singleton] at h
    have h2 : ∏ x ∈ S.filter (fun x => ¬ x = q0), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
        (((q1 : ℚ) + 1) / ((q1 : ℚ) - 1)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)) :=
      fiber_split (u0 := z) (k0 := s) (q0 := q1) (by omega) hq1 _
        (fun x hx => hS1 x (Finset.mem_filter.mp hx).1)
        (fun x hx k hk hks hkx => by
          obtain ⟨hx1, hne⟩ := Finset.mem_filter.mp hx
          have hx' : x = 2 ^ k * z - 1 := by omega
          rcases hs k hk hks (hx' ▸ (hLp x (hSL x hx1)).1) with h | h
          · exact absurd (hx'.trans h) hne
          · exact hx'.trans h)
    rw [← Finset.prod_filter_mul_prod_filter_not S (fun x => x = q0)]
    exact mul_le_mul h1 h2
      (Finset.prod_nonneg fun x hx => hB0 x (hSL x (Finset.mem_filter.mp hx).1))
      (le_trans zero_le_one (hBq q0 hq0))
  have hB' : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ z ^ 2 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
        (((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) * ((((q1 : ℚ) + 1) / ((q1 : ℚ) - 1)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2))) :=
    key _ (fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1) hj1
  rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => z ∣ x + 1))
    (fun x => z ^ 2 ∣ x + 1)]
  refine mul_le_mul hA hB' (Finset.prod_nonneg fun x hx => ?_) ?_
  · exact hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  · have h5 : (5 : ℚ) ≤ z := by exact_mod_cast hz5
    exact div_nonneg (by positivity) (by nlinarith)

/-- A kept parent `p` of `c` (`c` is the least odd prime factor of `p + 1` other than `z`, and `c ^ 2` does not
divide `p + 1`) has `p + 1 = c * (2 ^ i * z ^ j)`, or `p + 1 ≥ 2 * c * (c + 1)`. -/
theorem kept_parent_form {p c z : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hd : c ∣ p + 1)
    (hsq : ¬ c * c ∣ p + 1) (hpodd : p % 2 = 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') :
    (∃ i j : ℕ, p + 1 = c * (2 ^ i * z ^ j)) ∨ 2 * c * (c + 1) ≤ p + 1 := by
  obtain ⟨M, hM⟩ := hd
  have hM0 : M ≠ 0 := by
    rintro rfl
    omega
  by_cases hall : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ M → r = z
  · left
    obtain ⟨i, j, hij⟩ := two_pow_mul_pow_of_odd_primes_eq (M := M) (z := z) hM0 hall
    exact ⟨i, j, by rw [hM, hij]⟩
  · right
    push Not at hall
    obtain ⟨r, hr, hr2, hrM, hrz⟩ := hall
    have hrp : r ∣ p + 1 := by
      rw [hM]
      exact Dvd.dvd.mul_left hrM c
    have hcr : c ≤ r := hl r hr hr2 (by rw [Finset.mem_singleton]; exact hrz) hrp
    have hne : r ≠ c := by
      rintro rfl
      exact hsq (by rw [hM]; exact mul_dvd_mul_left r hrM)
    have hlt : c + 1 ≤ r := by omega
    have hMeven : 2 ∣ M := by
      have hcodd : c % 2 = 1 := by
        rcases hc.eq_two_or_odd with h | h
        · exact absurd h hc2
        · exact h
      have hprod : (c * M) % 2 = 0 := by
        rw [← hM]
        omega
      rw [Nat.mul_mod, hcodd] at hprod
      rcases Nat.mod_two_eq_zero_or_one M with h0 | h1
      · exact Nat.dvd_of_mod_eq_zero h0
      · rw [h1] at hprod
        norm_num at hprod
    have h2r : 2 * r ∣ M :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
        hMeven hrM
    have hMge : 2 * r ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) h2r
    calc 2 * c * (c + 1) ≤ 2 * c * r := Nat.mul_le_mul_left _ hlt
      _ = c * (2 * r) := by ring
      _ ≤ c * M := Nat.mul_le_mul_left _ hMge
      _ = p + 1 := hM.symm

/-- `table_master` with one more special prime `q0 ≥ 128` (in practice a leaf `q0 = 2 ^ k * z - 1`): its weight is
`bq ≥ (1 + 1/q0)(Nq+1)/(Nq-1)`, where every prime `q0 * 2 ^ i * z ^ j - 1` is at least `Nq` and
`Nq + 1 ≤ 2 q0 (q0 + 1)`, so that all kept parents of `q0` are at least `Nq` (`kept_parent_form`). -/
theorem table_master_q {m e z q0 Nq : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz17 : 17 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hzP : z ∉ P) (h5P : 5 ∈ P) (h5c : ∀ p ∈ P, ¬ 5 ∣ p + 1) (b7 b13 b31 b61 b103 b127 : ℚ)
    (h7 : 1 ≤ b7 ∧ (7 ∈ P → 8 / 7 ≤ b7 ∧ b7 ≤ 4 / 3 ∧ (b7 = 4 / 3 ∨ (∀ p ∈ P, ¬ 7 ∣ p + 1) ∨
      (13 ∈ P ∧ 8 / 7 * b13 ≤ b7) ∨ (13 ∉ P ∧ 8 / 7 * (182 / 180) ≤ b7))))
    (h13 : 1 ≤ b13 ∧ (13 ∈ P → 14 / 13 ≤ b13 ∧ b13 ≤ 7 / 6 ∧ (b13 = 7 / 6 ∨
      (∀ p ∈ P, ¬ 13 ∣ p + 1) ∨ (103 ∈ P ∧ 14 / 13 * b103 ≤ b13) ∨
      (103 ∉ P ∧ 14 / 13 * (884 / 882) ≤ b13))))
    (h31 : 1 ≤ b31 ∧ (31 ∈ P → 32 / 31 ≤ b31 ∧ b31 ≤ 16 / 15 ∧ (b31 = 16 / 15 ∨
      (∀ p ∈ P, ¬ 31 ∣ p + 1) ∨ (61 ∈ P ∧ 32 / 31 * b61 ≤ b31) ∨
      (61 ∉ P ∧ 32 / 31 * (992 / 990) ≤ b31))))
    (h61 : 1 ≤ b61 ∧ (61 ∈ P → 62 / 61 ≤ b61 ∧ b61 ≤ 31 / 30 ∧ (b61 = 31 / 30 ∨
      (∀ p ∈ P, ¬ 61 ∣ p + 1) ∨ 62 / 61 * (488 / 486) ≤ b61)))
    (h103 : 1 ≤ b103 ∧ (103 ∈ P → 104 / 103 ≤ b103 ∧ b103 ≤ 52 / 51 ∧ (b103 = 52 / 51 ∨
      (∀ p ∈ P, ¬ 103 ∣ p + 1) ∨ 104 / 103 * (824 / 822) ≤ b103)))
    (h127 : 1 ≤ b127 ∧ (127 ∈ P → 128 / 127 ≤ b127 ∧ b127 ≤ 64 / 63 ∧ (b127 = 64 / 63 ∨
      (∀ p ∈ P, ¬ 127 ∣ p + 1) ∨ 128 / 127 * (4064 / 4062) ≤ b127)))
    (hq0 : 128 ≤ q0) (hq0p : q0.Prime) (bq : ℚ) (hbqlo : 1 + 1 / (q0 : ℚ) ≤ bq)
    (hbqB : bq ≤ ((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) (hNq2 : 2 ≤ Nq)
    (hNq : Nq + 1 ≤ 2 * q0 * (q0 + 1))
    (hfar : ∀ i j : ℕ, (q0 * (2 ^ i * z ^ j) - 1).Prime → Nq ≤ q0 * (2 ^ i * z ^ j) - 1)
    (hbq : (1 + 1 / (q0 : ℚ)) * (((Nq : ℚ) + 1) / ((Nq : ℚ) - 1)) ≤ bq) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ((8 / 5 * b7 * b31 * b127 * (2048 / 2047)) *
          (bq * ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
            (((x : ℚ) + 1) / ((x : ℚ) - 1)))) := by
  classical
  have hne : ∀ c : ℕ, c < 128 → c ≠ q0 := fun c hc => by omega
  have hbq1 : (1 : ℚ) ≤ bq := le_trans (by
    have : (0 : ℚ) ≤ 1 / (q0 : ℚ) := by positivity
    linarith) hbqlo
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, F3, -, -, F6, -, -⟩ := facts hP hK E
  have hcz : ∀ c ∈ P, c ∉ ({z} : Finset ℕ) := fun c hc => by
    rw [Finset.mem_singleton]
    rintro rfl
    exact hzP hc
  obtain ⟨β, hβq, hβ3, hβ5, hβ7, hβ13, hβ31, hβ61, hβ103, hβ127, hβ⟩ : ∃ β : ℕ → ℚ, β q0 = bq ∧ β 3 = 8 / 5 ∧
      β 5 = 6 / 5 ∧ β 7 = b7 ∧ β 13 = b13 ∧ β 31 = b31 ∧ β 61 = b61 ∧ β 103 = b103 ∧ β 127 = b127 ∧
      ∀ x : ℕ, x ≠ q0 → x ≠ 3 → x ≠ 5 → x ≠ 7 → x ≠ 13 → x ≠ 31 → x ≠ 61 → x ≠ 103 → x ≠ 127 →
        β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = q0 then bq else if x = 3 then 8 / 5 else if x = 5 then 6 / 5 else if x = 7 then b7
      else if x = 13 then b13 else if x = 31 then b31 else if x = 61 then b61
      else if x = 103 then b103 else if x = 127 then b127 else ((x : ℚ) + 1) / ((x : ℚ) - 1),
      by simp, by simp [hne 3 (by norm_num)], by simp [hne 5 (by norm_num)],
      by simp [hne 7 (by norm_num)], by simp [hne 13 (by norm_num)], by simp [hne 31 (by norm_num)],
      by simp [hne 61 (by norm_num)], by simp [hne 103 (by norm_num)], by simp [hne 127 (by norm_num)],
      fun x h0 h1 h2 h3 h4 h5 h6 h7 h8 => by simp [h0, h1, h2, h3, h4, h5, h6, h7, h8]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases eq0 : p = q0
    · rw [eq0, hβq]
      exact ⟨hbqlo, hbqB⟩
    by_cases e3 : p = 3
    · subst e3
      rw [hβ3]
      norm_num
    by_cases e5 : p = 5
    · subst e5
      rw [hβ5]
      norm_num
    by_cases e7 : p = 7
    · subst e7
      obtain ⟨hlo, hhi, -⟩ := h7.2 hp
      rw [hβ7]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e13 : p = 13
    · subst e13
      obtain ⟨hlo, hhi, -⟩ := h13.2 hp
      rw [hβ13]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e31 : p = 31
    · subst e31
      obtain ⟨hlo, hhi, -⟩ := h31.2 hp
      rw [hβ31]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e61 : p = 61
    · subst e61
      obtain ⟨hlo, hhi, -⟩ := h61.2 hp
      rw [hβ61]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e103 : p = 103
    · subst e103
      obtain ⟨hlo, hhi, -⟩ := h103.2 hp
      rw [hβ103]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e127 : p = 127
    · subst e127
      obtain ⟨hlo, hhi, -⟩ := h127.2 hp
      rw [hβ127]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    rw [hβ p eq0 e3 e5 e7 e13 e31 e61 e103 e127]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) →
      c = q0 ∨ c = 3 ∨ c = 5 ∨ c = 7 ∨ c = 13 ∨ c = 31 ∨ c = 61 ∨ c = 103 ∨ c = 127 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (hβ c hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2.1 hcon.2.2.2.2.1 hcon.2.2.2.2.2.1
      hcon.2.2.2.2.2.2.1 hcon.2.2.2.2.2.2.2.1 hcon.2.2.2.2.2.2.2.2)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne'
    have hpp := (hP p hp).1
    have hwp := (hBd p hp).2
    rcases hsp c hne' with hcq | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hd' : q0 ∣ p + 1 := hcq ▸ hd
      have hcP' : q0 ∈ P := hcq ▸ hc
      have hodd : p % 2 = 1 := (hP p hp).1.eq_two_or_odd.resolve_left (hP p hp).2
      rw [hcq, hβq]
      rcases kept_parent_form (z := z) hq0p (by omega) hd'
        (F6 q0 hq0p (by omega) (hcz q0 hcP') p hp) hodd
        (fun c' h1 h2 h3 h4 => hcq ▸ hl c' h1 h2 h3 h4) with ⟨i, j, hij⟩ | hbig
      · have hpe : p = q0 * (2 ^ i * z ^ j) - 1 := by omega
        have hN : Nq ≤ p := by
          rw [hpe]
          exact hfar i j (hpe ▸ hpp)
        exact far_step (c := q0) (N := Nq) hNq2 hN hwp hbq
      · exact far_step (c := q0) (N := Nq) hNq2 (by omega) hwp hbq
    · have hp5 : p = 5 :=
        F3 3 Nat.prime_three (by norm_num) (hcz 3 hc) p hp 5 h5P hd (by norm_num)
      rw [hp5, hβ5, hβ3]
      norm_num
    · exact absurd hd (h5c p hp)
    · obtain ⟨-, -, hmenu⟩ := h7.2 hc
      rw [hβ7]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ7, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · have hpn : p = 13 :=
          F3 7 (by norm_num) (by norm_num) (hcz 7 hc) p hp 13 hnP hd (by norm_num)
        rw [hpn, hβ13]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx7 hz17 hpp hd (F6 7 (by norm_num) (by norm_num) (hcz 7 hc) p hp) hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 7) (N := 181) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h13.2 hc
      rw [hβ13]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ13, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · have hpn : p = 103 :=
          F3 13 (by norm_num) (by norm_num) (hcz 13 hc) p hp 103 hnP hd (by norm_num)
        rw [hpn, hβ103]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx13 hz17 hpp hd (F6 13 (by norm_num) (by norm_num) (hcz 13 hc) p hp) hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 13) (N := 883) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h31.2 hc
      rw [hβ31]
      rcases hmenu with heq | hcl | ⟨hnP, hw⟩ | ⟨hnn, hw⟩
      · exact absurd (by rw [hβ31, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · have hpn : p = 61 :=
          F3 31 (by norm_num) (by norm_num) (hcz 31 hc) p hp 61 hnP hd (by norm_num)
        rw [hpn, hβ61]
        refine le_trans (le_of_eq ?_) hw
        norm_num
      · rcases nx31 hz17 hpp hd hl with rfl | hfar
        · exact absurd hp hnn
        · exact far_step (c := 31) (N := 991) (by norm_num) hfar hwp
            (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h61.2 hc
      rw [hβ61]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ61, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · exact far_step (c := 61) (N := 487) (by norm_num) (nx61 hpp hd) hwp
          (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h103.2 hc
      rw [hβ103]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ103, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · exact far_step (c := 103) (N := 823) (by norm_num) (nx103 hz17 hpp hd hl) hwp
          (le_trans (le_of_eq (by norm_num)) hw)
    · obtain ⟨-, -, hmenu⟩ := h127.2 hc
      rw [hβ127]
      rcases hmenu with heq | hcl | hw
      · exact absurd (by rw [hβ127, heq]; norm_num) hne'
      · exact absurd hd (hcl p hp)
      · exact far_step (c := 127) (N := 4063) (by norm_num) (nx127 hz17 hpp hd hl) hwp
          (le_trans (le_of_eq (by norm_num)) hw)
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hM : ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hβ31, hβ127]
      exact ⟨by norm_num, h7.1, h31.1, h127.1⟩
  rw [hβ3, hβ7, hβ31, hβ127] at hM
  have hq0leaf : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => x = q0), β x ≤ bq := by
    have hsub : (L.filter (fun x => z ∣ x + 1)).filter (fun x => x = q0) ⊆ ({q0} : Finset ℕ) :=
      fun x hx => by
        rw [Finset.mem_singleton]
        exact (Finset.mem_filter.mp hx).2
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx _ => by
        rw [Finset.mem_singleton.mp hx, hβq]
        exact hbq1)
    rwa [Finset.prod_singleton, hβq] at h
  have hrest : ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0), β x ≤
      ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
  have hZ : ∏ x ∈ L.filter (fun x => z ∣ x + 1), β x ≤ bq *
      ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => z ∣ x + 1))
      (fun x => x = q0) β]
    exact mul_le_mul hq0leaf hrest (Finset.prod_nonneg fun x hx =>
      (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le) (by linarith)
  have hX : ∏ x ∈ L, β x ≤ (8 / 5 * b7 * b31 * b127 * (2048 / 2047)) *
      (bq * ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => z ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by
        have := h7.1
        have := h31.1
        have := h127.1
        positivity)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- Every prime `q0 * 2 ^ i * z ^ j - 1` is at least `Nq`, as soon as `Nq + 1 ≤ q0 * 2 ^ i0` with `2 ^ i0 ≤ 2 * z`,
`z ≥ 3` is odd and no `q0 * 2 ^ i - 1` with `i < i0` is prime (`q0 * z ^ j - 1` is even). -/
theorem far_of_small {q0 z Nq i0 : ℕ} (hq0 : 3 ≤ q0) (hq0odd : q0 % 2 = 1) (hz3 : 3 ≤ z)
    (hzodd : z % 2 = 1) (hi0 : 2 ^ i0 ≤ 2 * z) (hN : Nq + 1 ≤ q0 * 2 ^ i0)
    (h : ∀ i : ℕ, i < i0 → ¬ (q0 * 2 ^ i - 1).Prime) :
    ∀ i j : ℕ, (q0 * (2 ^ i * z ^ j) - 1).Prime → Nq ≤ q0 * (2 ^ i * z ^ j) - 1 := by
  intro i j hp
  have key : ∀ w : ℕ, 2 ^ i0 ≤ w → Nq ≤ q0 * w - 1 := fun w hw => by
    have := Nat.mul_le_mul_left q0 hw
    omega
  by_cases hj : j = 0
  · subst hj
    rw [pow_zero, mul_one] at hp ⊢
    by_cases hi : i < i0
    · exact absurd hp (h i hi)
    · exact key _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have hzj : z ≤ z ^ j := Nat.le_self_pow hj z
    by_cases hi : i = 0
    · subst hi
      rw [pow_zero, one_mul] at hp ⊢
      exfalso
      have hodd : (q0 * z ^ j) % 2 = 1 := by
        rw [Nat.mul_mod, Nat.pow_mod, hq0odd, hzodd]
        simp
      have hbig : 3 * 3 ≤ q0 * z ^ j := Nat.mul_le_mul hq0 (le_trans hz3 hzj)
      rcases hp.eq_two_or_odd with h2 | h2 <;> omega
    · apply key
      have h2i : 2 ≤ 2 ^ i :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 1 ≤ i by omega))
      have h3 : 2 * z ≤ 2 ^ i * z ^ j := Nat.mul_le_mul h2i hzj
      omega

/-- `zleaves_one` without the leaf `q0` itself: if `q0` is the only prime `2 ^ k * z - 1` with `1 ≤ k ≤ s`, the
leaves `x ≠ q0` with `z ∣ x + 1` weigh at most `z^2/(z^2-3) * u/(u-2)` with `u = 2 ^ s * z`. -/
theorem zleaves_except {z s q0 : ℕ} (hz : z.Prime) (hz5 : 5 ≤ z)
    (hs : ∀ k : ℕ, 1 ≤ k → k ≤ s → (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 = q0) {L : Finset ℕ}
    (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) :
    ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) *
        (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2)) := by
  classical
  have hzpow : ∀ k : ℕ, ¬ z ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow h)
    omega
  have hform : ∀ x ∈ L.filter (fun x => z ∣ x + 1),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * z ^ j := by
    intro x hx
    obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := z) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have hzo : Odd (z ^ j) := Odd.pow (hz.odd_of_ne_two (by omega))
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at hzo
      rcases hodd with ⟨u, hu⟩
      rcases hzo with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hxz
      exact hzpow k hxz
  have hB0 : ∀ x ∈ L, (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x hx).1.one_lt.le
  have hA : ∏ x ∈ ((L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0)).filter
        (fun x => z ^ 2 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) :=
    zleaf_bound (z := z) (by omega) 2 (by norm_num) _ (fun x hx => by
      obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
      obtain ⟨k, j, hk, hj, hkj⟩ := hform x (Finset.mem_filter.mp hx1).1
      refine ⟨k, j, hk, ?_, hkj⟩
      by_contra hj2
      have hj1 : j = 1 := by omega
      subst hj1
      rw [hkj, pow_one, pow_two] at hzz
      exact hzpow k (Nat.dvd_of_mul_dvd_mul_right hz.pos hzz))
  have hB' : ∏ x ∈ ((L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0)).filter
        (fun x => ¬ z ^ 2 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2) :=
    fiber_bound (u := 2 ^ s * z)
      (le_trans (by omega : 3 ≤ z) (Nat.le_mul_of_pos_left z (pow_pos (by norm_num) s))) _
      (fun x hx => by
        obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx2, hxq⟩ := Finset.mem_filter.mp hx1
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx2
        have hj1 : j = 1 := by
          by_contra hne
          apply hzz
          rw [hkj]
          exact Dvd.dvd.mul_left (pow_dvd_pow z (by omega)) _
        rw [hj1, pow_one] at hkj
        have hxL : x ∈ L := (Finset.mem_filter.mp hx2).1
        have hks : s < k := by
          by_contra hle
          have hx' : x = 2 ^ k * z - 1 := by omega
          apply hxq
          rw [hx']
          exact hs k hk (by omega) (hx' ▸ (hLp x hxL).1)
        refine ⟨k - s, by omega, ?_⟩
        rw [hkj, ← mul_assoc, ← pow_add]
        congr 2
        omega)
  rw [← Finset.prod_filter_mul_prod_filter_not
    ((L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0)) (fun x => z ^ 2 ∣ x + 1)]
  refine mul_le_mul hA hB' (Finset.prod_nonneg fun x hx => ?_) ?_
  · exact hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1
  · have h5 : (5 : ℚ) ≤ z := by exact_mod_cast hz5
    exact div_nonneg (by positivity) (by nlinarith)

/-- `zleaves_except` with a sharper bound for the leaves `2 ^ k * z ^ 2 - 1`: if none of them is prime for
`1 ≤ k ≤ s2`, the leaves `x ≠ q0` with `z ∣ x + 1` weigh at most `z^3/(z^3-3) * u2/(u2-2) * u/(u-2)` with
`u2 = 2 ^ s2 * z ^ 2` and `u = 2 ^ s * z`. -/
theorem zleaves_except2 {z s s2 q0 : ℕ} (hz : z.Prime) (hz5 : 5 ≤ z)
    (hs : ∀ k : ℕ, 1 ≤ k → k ≤ s → (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 = q0)
    (hs2 : ∀ k : ℕ, 1 ≤ k → k ≤ s2 → ¬ (2 ^ k * z ^ 2 - 1).Prime) {L : Finset ℕ}
    (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) :
    ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((z : ℚ) ^ 3 / ((z : ℚ) ^ 3 - 3)) *
        ((((2 ^ s2 * z ^ 2 : ℕ) : ℚ) / (((2 ^ s2 * z ^ 2 : ℕ) : ℚ) - 2)) *
          (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2))) := by
  classical
  have hzpow : ∀ k : ℕ, ¬ z ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow h)
    omega
  have hform : ∀ x ∈ L.filter (fun x => z ∣ x + 1),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * z ^ j := by
    intro x hx
    obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := z) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have hzo : Odd (z ^ j) := Odd.pow (hz.odd_of_ne_two (by omega))
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at hzo
      rcases hodd with ⟨u, hu⟩
      rcases hzo with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hxz
      exact hzpow k hxz
  have hB0 : ∀ x ∈ L, (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x hx).1.one_lt.le
  have hu2 : 3 ≤ 2 ^ s2 * z ^ 2 :=
    le_trans (le_trans (by omega : 3 ≤ z) (Nat.le_self_pow (by norm_num) z))
      (Nat.le_mul_of_pos_left (z ^ 2) (pow_pos (by norm_num) s2))
  have key : ∀ T : Finset ℕ,
      (∀ x ∈ T, x ∈ L ∧ ¬ x = q0 ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * z ^ j) →
      ∏ x ∈ T, (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
        ((z : ℚ) ^ 3 / ((z : ℚ) ^ 3 - 3)) *
          ((((2 ^ s2 * z ^ 2 : ℕ) : ℚ) / (((2 ^ s2 * z ^ 2 : ℕ) : ℚ) - 2)) *
            (((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2))) := by
    intro T hT
    have hA : ∏ x ∈ T.filter (fun x => z ^ 3 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
        (z : ℚ) ^ 3 / ((z : ℚ) ^ 3 - 3) :=
      zleaf_bound (z := z) (by omega) 3 (by norm_num) _ (fun x hx => by
        obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
        obtain ⟨-, -, k, j, hk, hj, hkj⟩ := hT x hx1
        refine ⟨k, j, hk, ?_, hkj⟩
        by_contra hj3
        have hj2 : j ≤ 2 := by omega
        have h3 : z ^ 3 = z ^ j * z ^ (3 - j) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hkj, h3, mul_comm (2 ^ k)] at hzz
        have hd : z ^ (3 - j) ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_left (pow_pos hz.pos j) hzz
        exact hzpow k (dvd_trans (dvd_pow_self z (by omega)) hd))
    have hB2 : ∏ x ∈ (T.filter (fun x => ¬ z ^ 3 ∣ x + 1)).filter (fun x => z ^ 2 ∣ x + 1),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
          ((2 ^ s2 * z ^ 2 : ℕ) : ℚ) / (((2 ^ s2 * z ^ 2 : ℕ) : ℚ) - 2) :=
      fiber_bound (u := 2 ^ s2 * z ^ 2) hu2 _ (fun x hx => by
        obtain ⟨hx1, hz2⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx2, hz3⟩ := Finset.mem_filter.mp hx1
        obtain ⟨hxL, -, k, j, hk, hj, hkj⟩ := hT x hx2
        have h1 : 2 ≤ j := by
          by_contra hlt
          have hj1 : j = 1 := by omega
          subst hj1
          rw [hkj, pow_one, pow_two] at hz2
          exact hzpow k (Nat.dvd_of_mul_dvd_mul_right hz.pos hz2)
        have h2 : j ≤ 2 := by
          by_contra hgt
          apply hz3
          rw [hkj]
          exact Dvd.dvd.mul_left (pow_dvd_pow z (by omega)) _
        have hj2 : j = 2 := by omega
        rw [hj2] at hkj
        have hks : s2 < k := by
          by_contra hle
          have hx' : x = 2 ^ k * z ^ 2 - 1 := by omega
          exact hs2 k hk (by omega) (hx' ▸ (hLp x hxL).1)
        refine ⟨k - s2, by omega, ?_⟩
        rw [hkj, ← mul_assoc, ← pow_add]
        congr 2
        omega)
    have hB1 : ∏ x ∈ (T.filter (fun x => ¬ z ^ 3 ∣ x + 1)).filter (fun x => ¬ z ^ 2 ∣ x + 1),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
          ((2 ^ s * z : ℕ) : ℚ) / (((2 ^ s * z : ℕ) : ℚ) - 2) :=
      fiber_bound (u := 2 ^ s * z)
        (le_trans (by omega : 3 ≤ z) (Nat.le_mul_of_pos_left z (pow_pos (by norm_num) s))) _
        (fun x hx => by
          obtain ⟨hx1, hzz⟩ := Finset.mem_filter.mp hx
          obtain ⟨hx2, -⟩ := Finset.mem_filter.mp hx1
          obtain ⟨hxL, hxq, k, j, hk, hj, hkj⟩ := hT x hx2
          have hj1 : j = 1 := by
            by_contra hne
            apply hzz
            rw [hkj]
            exact Dvd.dvd.mul_left (pow_dvd_pow z (by omega)) _
          rw [hj1, pow_one] at hkj
          have hks : s < k := by
            by_contra hle
            have hx' : x = 2 ^ k * z - 1 := by omega
            apply hxq
            rw [hx']
            exact hs k hk (by omega) (hx' ▸ (hLp x hxL).1)
          refine ⟨k - s, by omega, ?_⟩
          rw [hkj, ← mul_assoc, ← pow_add]
          congr 2
          omega)
    have hn : ∀ S : Finset ℕ, S ⊆ T → (0 : ℚ) ≤ ∏ x ∈ S, (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
      fun S hS => Finset.prod_nonneg fun x hx => hB0 x (hT x (hS hx)).1
    have h125 : (125 : ℚ) ≤ (z : ℚ) ^ 3 := by
      have h' : 125 ≤ z ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hz5 3)
      exact_mod_cast h'
    have hu2q : (3 : ℚ) ≤ ((2 ^ s2 * z ^ 2 : ℕ) : ℚ) := by exact_mod_cast hu2
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun x => z ^ 3 ∣ x + 1),
      ← Finset.prod_filter_mul_prod_filter_not (T.filter (fun x => ¬ z ^ 3 ∣ x + 1))
        (fun x => z ^ 2 ∣ x + 1)]
    refine mul_le_mul hA (mul_le_mul hB2 hB1 ?_ ?_) ?_ ?_
    · exact hn _ (fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    · exact div_nonneg (by positivity) (by linarith)
    · exact mul_nonneg
        (hn _ (fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1))
        (hn _ (fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1))
    · exact div_nonneg (by positivity) (by linarith)
  exact key _ (fun x hx =>
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2,
      hform x (Finset.mem_filter.mp hx).1⟩)

/-- `amod4_leaf` with the leaf `q0` weighed separately (`table_master_q`): `bq` for `q0` and `Zb` for the other
leaves `x` with `z ∣ x + 1`. -/
theorem amod4_leafq {m e z q0 Nq : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz17 : 17 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hzP : z ∉ P) (hm4 : m % 4 = 2) (hm : 22 ≤ m) (he : 3 ≤ e)
    (hq0 : 128 ≤ q0) (hq0p : q0.Prime) (bq : ℚ) (hbqlo : 1 + 1 / (q0 : ℚ) ≤ bq)
    (hbqB : bq ≤ ((q0 : ℚ) + 1) / ((q0 : ℚ) - 1)) (hNq2 : 2 ≤ Nq)
    (hNq : Nq + 1 ≤ 2 * q0 * (q0 + 1))
    (hfar : ∀ i j : ℕ, (q0 * (2 ^ i * z ^ j) - 1).Prime → Nq ≤ q0 * (2 ^ i * z ^ j) - 1)
    (hbq : (1 + 1 / (q0 : ℚ)) * (((Nq : ℚ) + 1) / ((Nq : ℚ) - 1)) ≤ bq)
    (Zb : ℚ) (hZb0 : 0 ≤ Zb)
    (hZ : ∀ L : Finset ℕ, L ⊆ P → (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) →
      ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ Zb)
    (hnum : (1 + 1 / (2 : ℚ) ^ 22) * (((1 + z ^ 3 : ℕ) : ℚ) / ((z ^ 3 : ℕ) : ℚ)) *
      ((8 / 5 * (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) * 1 * 1 * (2048 / 2047)) *
        (bq * Zb)) < 2) :
    False := by
  classical
  obtain ⟨h3P, h5P, h5c, -⟩ := setup5 hP hz (by omega) E hm4
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨F1, -, -, -, -, -, -, -⟩ := facts hP hK E
  have h7z : (7 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have hbq0 : (0 : ℚ) ≤ bq := le_trans (by positivity) hbqlo
  have hfac0 : (0 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ 22) * (((1 + z ^ 3 : ℕ) : ℚ) / ((z ^ 3 : ℕ) : ℚ)) := by
    positivity
  have hfin : ∀ C : ℚ, 0 ≤ C →
      C ≤ 8 / 5 * (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) * 1 * 1 * (2048 / 2047) →
      (∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
        (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
          (C * (bq * ∏ x ∈ (L.filter (fun x => z ∣ x + 1)).filter (fun x => ¬ x = q0),
            (((x : ℚ) + 1) / ((x : ℚ) - 1))))) → False := by
    rintro C hC0 hC ⟨L, hLP, hleaf, hmain⟩
    exact table_close hm hmain (by positivity) (kk_le (by omega) (le_refl z) he) hC0
      (mul_nonneg hbq0 (Finset.prod_nonneg fun x hx =>
        B_nonneg (hP x (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)).1.one_lt.le))
      (mul_le_mul_of_nonneg_left (hZ L hLP hleaf) hbq0)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hC (mul_nonneg hbq0 hZb0)) hfac0) hnum)
  by_cases h13 : 13 ∈ P
  · have h7 : 7 ∈ P := F1 7 (by norm_num) (by norm_num) h7z 13 h13 (by norm_num)
    by_cases h31 : 31 ∈ P
    · exact kill_7_13_31 hP hz E h3P h5P h7 h13 h31
    · by_cases h103 : 103 ∈ P
      · by_cases h127 : 127 ∈ P
        · exact kill_7_13_103_127 hP hz E h3P h5P h7 h13 h103 h127
        · -- 7 <- 13 <- 103, kept parents of 103 at least 823; 31 and 127 are not simple
          exact hfin _ (by norm_num) (le_refl _)
            (table_master_q hP hz hz17 E hzP h5P h5c
              (8 / 7 * (14 / 13 * (104 / 103 * (824 / 822)))) (14 / 13 * (104 / 103 * (824 / 822))) 1
              (31 / 30) (104 / 103 * (824 / 822)) 1
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h103, le_refl _⟩))⟩⟩
              ⟨le_refl _, fun h => absurd h h31⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
              ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
              ⟨le_refl _, fun h => absurd h h127⟩
              hq0 hq0p bq hbqlo hbqB hNq2 hNq hfar hbq)
      · -- 7 <- 13, kept parents of 13 at least 883; 31 is not simple
        exact hfin _ (by norm_num) (by norm_num)
          (table_master_q hP hz hz17 E hzP h5P h5c
            (8 / 7 * (14 / 13 * (884 / 882))) (14 / 13 * (884 / 882)) 1
            (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inl ⟨h13, le_refl _⟩))⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h103, le_refl _⟩))⟩⟩
            ⟨le_refl _, fun h => absurd h h31⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
            ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
            hq0 hq0p bq hbqlo hbqB hNq2 hNq hfar hbq)
  · -- 13 is not simple: kept parents of 7 at least 181
    exact hfin _ (by norm_num) (by norm_num)
      (table_master_q hP hz hz17 E hzP h5P h5c
        (8 / 7 * (182 / 180)) 1 (16 / 15)
        (31 / 30) (52 / 51) (128 / 127 * (4064 / 4062))
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (Or.inr ⟨h13, le_refl _⟩))⟩⟩
        ⟨le_refl _, fun h => absurd h h13⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, Or.inl rfl⟩⟩
        ⟨by norm_num, fun _ => ⟨by norm_num, by norm_num, Or.inr (Or.inr (le_refl _))⟩⟩
        hq0 hq0p bq hbqlo hbqB hNq2 hNq hfar hbq)

/-- `8 ∣ e`, `a = 2 (mod 4)` and `z` one of `29`, `43`, `47`, `59` or of 113 primes between `61` and `823`:
`a ≤ 21` (`amod4_skip`, `amod4_leaf`, `amod4_leafq`). -/
theorem amod4_dead_mid {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) (he : n.factorization z % 8 = 0)
    (hl : z ∈ ({29, 43, 47, 59, 67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181,
      191, 193, 197, 211, 223, 227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
      307, 311, 313, 317, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
      421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523,
      541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643,
      647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761,
      769, 773, 787, 797, 809, 811, 821} : Finset ℕ))
    (h4 : padicValNat 2 n % 4 = 2) : padicValNat 2 n ≤ 21 := by
  by_contra hgt
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS z).mpr rfl).2.2
  have hzP : z ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)) := fun hmem =>
    (Finset.mem_filter.mp hmem).2 (Finset.mem_singleton_self z)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 463) (Nq := 14815)
      (by norm_num) (by norm_num) ((1 + 1 / 463) * (14816 / 14814)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except2 (s := 15) (s2 := 4) (q0 := 463) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 4
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun k h1 h2 => by interval_cases k <;> norm_num)
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 7) (q0 := 5503) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 7
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 751) (Nq := 6007)
      (by norm_num) (by norm_num) ((1 + 1 / 751) * (6008 / 6006)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except2 (s := 13) (s2 := 4) (q0 := 751) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 4
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun k h1 h2 => by interval_cases k <;> norm_num)
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 12) (q0 := 241663) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 12
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 4) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 4) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 5) (q0 := 1423) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 4
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 3) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 823) (Nq := 49379)
      (by norm_num) (by norm_num) ((1 + 1 / 823) * (49380 / 49378)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except (s := 4) (q0 := 823) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 3
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 3) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 3) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 3) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 3) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 523) (Nq := 31379)
      (by norm_num) (by norm_num) ((1 + 1 / 523) * (31380 / 31378)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except (s := 5) (q0 := 523) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 2
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 3) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 3) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 4) (q0 := 1303) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 3
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 3) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 6) (q0 := 787) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 2
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 421) (Nq := 25259)
      (by norm_num) (by norm_num) ((1 + 1 / 421) * (25260 / 25258)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except (s := 5) (q0 := 421) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 907) (Nq := 29023)
      (by norm_num) (by norm_num) ((1 + 1 / 907) * (29024 / 29022)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except (s := 3) (q0 := 907) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 2
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 3) (q0 := 1051) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 2
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 541) (Nq := 4327)
      (by norm_num) (by norm_num) ((1 + 1 / 541) * (4328 / 4326)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except (s := 4) (q0 := 541) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 3) (q0 := 1123) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 2
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 3) (q0 := 1171) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 2
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 613) (Nq := 4903)
      (by norm_num) (by norm_num) ((1 + 1 / 613) * (4904 / 4902)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except (s := 3) (q0 := 613) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 2) (fun k h1 h2 => by interval_cases k <;> norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 673) (Nq := 40379)
      (by norm_num) (by norm_num) ((1 + 1 / 673) * (40380 / 40378)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except (s := 3) (q0 := 673) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leafq hP hz (by norm_num) E hzP h4 (by omega) (by omega) (q0 := 733) (Nq := 43979)
      (by norm_num) (by norm_num) ((1 + 1 / 733) * (43980 / 43978)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (far_of_small (i0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun i hi => by interval_cases i <;> norm_num))
      (by norm_num) _ (by norm_num)
      (fun L hLP hleaf => zleaves_except (s := 2) (q0 := 733) hz (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 5) (q0 := 757) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_two (s := 12) (q0 := 877) (q1 := 3511) hz (by norm_num)
        (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            left
            norm_num
          · by_cases hk3 : k = 3
            · subst hk3
              right
              norm_num
            · exfalso
              interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 3) (q0 := 997) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 2) (q0 := 1093) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 2) (q0 := 1153) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 2) (q0 := 1201) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 2) (q0 := 1213) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 2) (q0 := 1237) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_leaf hP hz (by norm_num) E hzP h4 (by omega) (by omega) _ (by norm_num)
      (fun L hLP hleaf => zleaves_one (s := 2) (q0 := 1321) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp))
        (fun x hx => hP x (hLP hx)) hleaf)
      (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 1) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)
  · exact amod4_skip hP hz (by norm_num) E hzP (s := 0) (fun k h1 h2 => by omega) h4 (by omega) (by omega) (by norm_num)

/-- The weights argument for `a` odd with separate weights for `7` and `31` (not simple, without consumer, or
default): `3 ∣ 2 ^ a + 1` is the source of `3`, so `3` weighs `4/3`. -/
theorem odd_master_b {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz5 : 5 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hmo : m % 2 = 1) (b7 b31 : ℚ)
    (h7 : 1 ≤ b7 ∧ (7 ∈ P → 8 / 7 ≤ b7 ∧ b7 ≤ 4 / 3 ∧ (b7 ≠ 4 / 3 → ∀ p ∈ P, ¬ 7 ∣ p + 1)))
    (h31 : 1 ≤ b31 ∧
      (31 ∈ P → 32 / 31 ≤ b31 ∧ b31 ≤ 16 / 15 ∧ (b31 ≠ 16 / 15 → ∀ p ∈ P, ¬ 31 ∣ p + 1))) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ((4 / 3 * b7 * b31 * (64 / 63) * (2048 / 2047)) *
          ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, -, F4, -, -, -, -⟩ := facts hP hK E
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have hno3 : ∀ p ∈ P, ¬ 3 ∣ p + 1 :=
    F4 3 Nat.prime_three (by norm_num) h3z (three_dvd_two_pow_add_one hmo)
  obtain ⟨β, hβ3, hβ7, hβ31, hβ⟩ : ∃ β : ℕ → ℚ, β 3 = 4 / 3 ∧ β 7 = b7 ∧ β 31 = b31 ∧
      ∀ x : ℕ, x ≠ 3 → x ≠ 7 → x ≠ 31 → β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = 3 then 4 / 3 else if x = 7 then b7 else if x = 31 then b31
      else ((x : ℚ) + 1) / ((x : ℚ) - 1), by simp, by simp, by simp,
      fun x h1 h2 h3 => by simp [h1, h2, h3]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [hβ3]
      norm_num
    by_cases e7 : p = 7
    · subst e7
      obtain ⟨hlo, hhi, -⟩ := h7.2 hp
      rw [hβ7]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases e31 : p = 31
    · subst e31
      obtain ⟨hlo, hhi, -⟩ := h31.2 hp
      rw [hβ31]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    rw [hβ p e3 e7 e31]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → c = 3 ∨ c = 7 ∨ c = 31 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (hβ c hcon.1 hcon.2.1 hcon.2.2)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne
    rcases hsp c hne with rfl | rfl | rfl
    · exact absurd hd (hno3 p hp)
    · have hne' : b7 ≠ 4 / 3 := by
        intro hb
        apply hne
        rw [hβ7, hb]
        norm_num
      exact absurd hd ((h7.2 hc).2.2 hne' p hp)
    · have hne' : b31 ≠ 16 / 15 := by
        intro hb
        apply hne
        rw [hβ31, hb]
        norm_num
      exact absurd hd ((h31.2 hc).2.2 hne' p hp)
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hd127 := hβ 127 (by norm_num) (by norm_num) (by norm_num)
  have e127 : (((127 : ℕ) : ℚ) + 1) / (((127 : ℕ) : ℚ) - 1) = 64 / 63 := by norm_num
  rw [e127] at hd127
  have hM : ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hβ31, hd127]
      exact ⟨by norm_num, h7.1, h31.1, by norm_num⟩
  rw [hβ3, hβ7, hβ31, hd127] at hM
  have hZ : ∏ x ∈ L.filter (fun x => z ∣ x + 1), β x ≤
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod (fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp hx).1)
  have hX : ∏ x ∈ L, β x ≤ (4 / 3 * b7 * b31 * (64 / 63) * (2048 / 2047)) *
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => z ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by
        have := h7.1
        have := h31.1
        positivity)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- `z = 7`, `a` odd, `a ≥ 5`: no solution. Total at most `1.92472`. -/
theorem odd_seven {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hzP : 7 ∉ P) (hmo : m % 2 = 1) (hm : 5 ≤ m) (he : 2 ≤ e) : False := by
  have hz : Nat.Prime 7 := by norm_num
  obtain ⟨L, hLP, hleaf, hmain⟩ := odd_master_b hP hz (by norm_num) E hmo 1 (16 / 15)
    ⟨le_refl _, fun h => absurd h hzP⟩
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
  have hZ := seven_leaves (fun x hx => hP x (hLP hx)) hleaf
  refine table_close hm hmain (by positivity)
    (kk_le (a := 7) (b := 2) (by norm_num) (le_refl _) he) (by norm_num)
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) hZ ?_
  norm_num

/-- `z = 31`, `a` odd, `a ≥ 7`: no solution. Total at most `1.95471`. -/
theorem odd_thirtyone {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 31 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 31 ^ e * ∏ p ∈ P, p)
    (hzP : 31 ∉ P) (hmo : m % 2 = 1) (hm : 7 ≤ m) (he : 2 ≤ e) : False := by
  have hz : Nat.Prime 31 := by norm_num
  exact table_finish hP hz (by norm_num) (le_refl 31) hm he (by norm_num)
    (odd_master_b hP hz (by norm_num) E hmo (4 / 3) 1
      ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
      ⟨le_refl _, fun h => absurd h hzP⟩)
    (by norm_num)

/-- `z = 7` or `z = 31`, `4 ∣ a` and the exact power of `2` in `a` at least `2 ^ 11`: no solution. -/
theorem four_dvd_small {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime)
    (hl : z = 7 ∨ z = 31) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (h4 : padicValNat 2 n % 4 = 0)
    (h8 : padicValNat 2 n % 8 ≠ 4) (h16 : padicValNat 2 n % 16 ≠ 8) (h32 : padicValNat 2 n % 32 ≠ 16)
    (h64 : padicValNat 2 n % 64 ≠ 32) (h128 : padicValNat 2 n % 128 ≠ 64)
    (h256 : padicValNat 2 n % 256 ≠ 128) (h512 : padicValNat 2 n % 512 ≠ 256)
    (h1024 : padicValNat 2 n % 1024 ≠ 512) (h2048 : padicValNat 2 n % 2048 ≠ 1024) :
    padicValNat 2 n = 0 := by
  classical
  by_contra hm0
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS z).mpr rfl).2.2
  have hzP : z ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)) := fun hmem =>
    (Finset.mem_filter.mp hmem).2 (Finset.mem_singleton_self z)
  have hme : Even (padicValNat 2 n) := Nat.even_iff.mpr (by omega)
  obtain ⟨c, k, t, hc, hc2, hc3, hcm, hk, hcF, ht, hmt⟩ := exists_fermat_prime hm0 hme
  have hk11 : 11 ≤ k := v2_large ht hmt h4 h8 h16 h32 h64 h128 h256 h512 h1024 h2048
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ n.factorization z → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, F2, -, -, -, -, -, -⟩ := facts hP hK E
  have hd := two_pow_succ_dvd_pred hc hcF
  have hc4097 : 4097 ≤ c := by
    have h12 : 2 ^ 12 ∣ c - 1 := (pow_dvd_pow 2 (by omega : 12 ≤ k + 1)).trans hd
    have hc2' := hc.two_le
    have hle := Nat.le_of_dvd (by omega) h12
    norm_num at hle
    omega
  have hz31 : z ≤ 31 := by
    rcases hl with rfl | rfl <;> norm_num
  have hcz : c ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    intro hcz'
    exact absurd (hcz' ▸ hc4097) (Nat.not_le.mpr (lt_of_le_of_lt hz31 (by norm_num)))
  have hcP := F2 c hc hc2 hcz hcm
  have h3c : 3 ∣ c + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hm11 : 11 ≤ padicValNat 2 n := by
    have h1 : 2048 ≤ 2 ^ k := by
      calc 2048 = 2 ^ 11 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk11
    have ht1 : 1 ≤ t := by
      obtain ⟨s, rfl⟩ := ht
      omega
    have h2 : 2 ^ k * 1 ≤ 2 ^ k * t := Nat.mul_le_mul_left _ ht1
    omega
  rcases hl with rfl | rfl
  · exact pinned_seven hP E hzP hcP h3c hc4097 hm11 he2
  · exact pinned_thirtyone hP E hzP hcP h3c hc4097 hm11 he2

/-- `z = 7` or `z = 31` with `8 ∣ e`: `a ≤ 21`. -/
theorem small_dead {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime)
    (hl : z = 7 ∨ z = 31) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (he : n.factorization z % 8 = 0)
    (h8 : padicValNat 2 n % 8 ≠ 4) (h16 : padicValNat 2 n % 16 ≠ 8) (h32 : padicValNat 2 n % 32 ≠ 16)
    (h64 : padicValNat 2 n % 64 ≠ 32) (h128 : padicValNat 2 n % 128 ≠ 64)
    (h256 : padicValNat 2 n % 256 ≠ 128) (h512 : padicValNat 2 n % 512 ≠ 256)
    (h1024 : padicValNat 2 n % 1024 ≠ 512) (h2048 : padicValNat 2 n % 2048 ≠ 1024) :
    padicValNat 2 n ≤ 21 := by
  by_contra hgt
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS z).mpr rfl).2.2
  have hzP : z ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)) := fun hmem =>
    (Finset.mem_filter.mp hmem).2 (Finset.mem_singleton_self z)
  rcases (by omega : padicValNat 2 n % 4 = 2 ∨ padicValNat 2 n % 4 = 0 ∨
    padicValNat 2 n % 2 = 1) with c | c | c
  · rcases hl with rfl | rfl
    · exact amod4_7 hP E hzP c (by omega) (by omega)
    · exact amod4_31 hP E hzP c (by omega) (by omega)
  · have h0 := four_dvd_small h hz hl hS c h8 h16 h32 h64 h128 h256 h512 h1024 h2048
    omega
  · rcases hl with rfl | rfl
    · exact odd_seven hP E hzP c (by omega) he2
    · exact odd_thirtyone hP E hzP c (by omega) he2

/-- `a` odd with any bound `Zb` for the leaves `x` with `z ∣ x + 1`: no solution when the total is below `2`. -/
theorem odd_leaf {m e z a0 e0 : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz5 : 5 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hmo : m % 2 = 1) (hm : a0 ≤ m) (he : e0 ≤ e) (Zb : ℚ)
    (hZ : ∀ L : Finset ℕ, L ⊆ P → (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) →
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ Zb)
    (hnum : (1 + 1 / (2 : ℚ) ^ a0) * (((1 + z ^ e0 : ℕ) : ℚ) / ((z ^ e0 : ℕ) : ℚ)) *
      ((4 / 3 * (4 / 3) * (16 / 15) * (64 / 63) * (2048 / 2047)) * Zb) < 2) : False := by
  obtain ⟨L, hLP, hleaf, hmain⟩ := odd_master hP hz hz5 E hmo
  exact table_close hm hmain (by positivity) (kk_le (by omega) (le_refl z) he) (by norm_num)
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) (hZ L hLP hleaf) hnum

/-- `3` pinned under a simple prime `q ≥ 4097`, with any bound `Zb` for the leaves `x` with `z ∣ x + 1`. -/
theorem pinned_leaf {m e z q e0 : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz5 : 5 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hqP : q ∈ P) (h3q : 3 ∣ q + 1) (hq : 4097 ≤ q) (hm : 11 ≤ m) (he : e0 ≤ e) (Zb : ℚ)
    (hZ : ∀ L : Finset ℕ, L ⊆ P → (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) →
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ Zb)
    (hnum : (1 + 1 / (2 : ℚ) ^ 11) * (((1 + z ^ e0 : ℕ) : ℚ) / ((z ^ e0 : ℕ) : ℚ)) *
      ((4 / 3 * (4098 / 4096) * (4 / 3) * (16 / 15) * (64 / 63) * (2048 / 2047)) * Zb) < 2) :
    False := by
  obtain ⟨L, hLP, hleaf, hmain⟩ := pinned_master hP hz hz5 E hqP h3q hq (4 / 3) (16 / 15)
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
  exact table_close hm hmain (by positivity) (kk_le (by omega) (le_refl z) he) (by norm_num)
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) (hZ L hLP hleaf) hnum

theorem odd_ge_nine {a : ℕ} (h : ¬ a ≤ 7) (c : a % 2 = 1) : 9 ≤ a := by omega

theorem four_dvd_of_not {a : ℕ} (c : ¬ a % 2 = 1) (hna : a % 4 ≠ 2) : a % 4 = 0 := by omega

/-- A prime `c` with `2 ^ (k + 1) ∣ c - 1` and `k ≥ 11` is at least `4097`. -/
theorem ge_4097 {c k : ℕ} (hc : c.Prime) (hk : 11 ≤ k) (hd : 2 ^ (k + 1) ∣ c - 1) :
    4097 ≤ c := by
  have h12 : 2 ^ 12 ∣ c - 1 := (pow_dvd_pow 2 (by omega : 12 ≤ k + 1)).trans hd
  have hc2' := hc.two_le
  have hle := Nat.le_of_dvd (by omega) h12
  norm_num at hle
  omega

theorem ge_eleven {m k t : ℕ} (hk : 11 ≤ k) (ht : Odd t) (hm : m = 2 ^ k * t) : 11 ≤ m := by
  have h1 : 2048 ≤ 2 ^ k := by
    calc 2048 = 2 ^ 11 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have ht1 : 1 ≤ t := by
    obtain ⟨s, rfl⟩ := ht
    omega
  have h2 : 2 ^ k * 1 ≤ 2 ^ k * t := Nat.mul_le_mul_left _ ht1
  omega

/-- One prime `5 ≤ z < 4097` with a bound `Zb` for its leaves: if `a` is not `2 (mod 4)` and the exact power of
`2` in `a` is none of `2 ^ 2, ..., 2 ^ 10`, then `a ≤ 7` (`a` odd: `3` has no consumer; `4 ∣ a`: `3` is pinned
under the Fermat prime). -/
theorem small_core {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz5 : 5 ≤ z)
    (hz4097 : z < 4097) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (hna : padicValNat 2 n % 4 ≠ 2)
    (h8 : padicValNat 2 n % 8 ≠ 4) (h16 : padicValNat 2 n % 16 ≠ 8) (h32 : padicValNat 2 n % 32 ≠ 16)
    (h64 : padicValNat 2 n % 64 ≠ 32) (h128 : padicValNat 2 n % 128 ≠ 64)
    (h256 : padicValNat 2 n % 256 ≠ 128) (h512 : padicValNat 2 n % 512 ≠ 256)
    (h1024 : padicValNat 2 n % 1024 ≠ 512) (h2048 : padicValNat 2 n % 2048 ≠ 1024) (Zb : ℚ)
    (hZ : ∀ L : Finset ℕ, (∀ x ∈ L, x.Prime ∧ x ≠ 2) →
      (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) →
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ Zb)
    (hodd : (1 + 1 / (2 : ℚ) ^ 9) * (((1 + z ^ 2 : ℕ) : ℚ) / ((z ^ 2 : ℕ) : ℚ)) *
      ((4 / 3 * (4 / 3) * (16 / 15) * (64 / 63) * (2048 / 2047)) * Zb) < 2)
    (hpin : (1 + 1 / (2 : ℚ) ^ 11) * (((1 + z ^ 2 : ℕ) : ℚ) / ((z ^ 2 : ℕ) : ℚ)) *
      ((4 / 3 * (4098 / 4096) * (4 / 3) * (16 / 15) * (64 / 63) * (2048 / 2047)) * Zb) < 2) :
    padicValNat 2 n ≤ 7 := by
  classical
  by_contra hgt
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS z).mpr rfl).2.2
  by_cases c : padicValNat 2 n % 2 = 1
  · exact odd_leaf hP hz hz5 E c (odd_ge_nine hgt c) he2 Zb
      (fun L hLP hleaf => hZ L (fun x hx => hP x (hLP hx)) hleaf) hodd
  · have h4 : padicValNat 2 n % 4 = 0 := four_dvd_of_not c hna
    have hm0 : padicValNat 2 n ≠ 0 := fun h0 => hgt (by rw [h0]; norm_num)
    have hme : Even (padicValNat 2 n) := Nat.even_iff.mpr
      ((Nat.mod_two_eq_zero_or_one (padicValNat 2 n)).resolve_right c)
    obtain ⟨c', k, t, hc, hc2, hc3, hcm, hk, hcF, ht, hmt⟩ := exists_fermat_prime hm0 hme
    have hk11 : 11 ≤ k := v2_large ht hmt h4 h8 h16 h32 h64 h128 h256 h512 h1024 h2048
    have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ n.factorization z → c ∈ ({z} : Finset ℕ) :=
      fun c hc hcd =>
        Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
    obtain ⟨-, F2, -, -, -, -, -, -⟩ := facts hP hK E
    have hc4097 : 4097 ≤ c' := ge_4097 hc hk11 (two_pow_succ_dvd_pred hc hcF)
    have hcz : c' ∉ ({z} : Finset ℕ) := by
      rw [Finset.mem_singleton]
      intro hcz'
      exact absurd (hcz' ▸ hc4097) (Nat.not_le.mpr hz4097)
    have hcP := F2 c' hc hc2 hcz hcm
    have h3c : 3 ∣ c' + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hc3])
    exact pinned_leaf hP hz hz5 E hcP h3c hc4097 (ge_eleven hk11 ht hmt) he2 Zb
      (fun L hLP hleaf => hZ L (fun x hx => hP x (hLP hx)) hleaf) hpin

/-- `z` in `{23, 29, 37, 41, 43, 47, 53, 59}`: if `a` is not `2 (mod 4)` and the exact power of `2` in `a` is none
of `2 ^ 2, ..., 2 ^ 10`, then `a ≤ 7`. Totals at most `1.99731` (`a` odd, `a ≥ 9`) and `1.99536` (`4 ∣ a`). -/
theorem small8_dead {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime)
    (hl : z ∈ ({23, 29, 37, 41, 43, 47, 53, 59} : Finset ℕ))
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) (hna : padicValNat 2 n % 4 ≠ 2)
    (h8 : padicValNat 2 n % 8 ≠ 4) (h16 : padicValNat 2 n % 16 ≠ 8) (h32 : padicValNat 2 n % 32 ≠ 16)
    (h64 : padicValNat 2 n % 64 ≠ 32) (h128 : padicValNat 2 n % 128 ≠ 64)
    (h256 : padicValNat 2 n % 256 ≠ 128) (h512 : padicValNat 2 n % 512 ≠ 256)
    (h1024 : padicValNat 2 n % 1024 ≠ 512) (h2048 : padicValNat 2 n % 2048 ≠ 1024) :
    padicValNat 2 n ≤ 7 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_core h hz (by norm_num) (by norm_num) hS hna h8 h16 h32 h64 h128 h256 h512 h1024 h2048 _
      (fun L hLp hleaf => zleaves_skip (s := 2) hz (by norm_num) (fun k h1 h2 => by interval_cases k <;> norm_num) hLp hleaf)
      (by norm_num) (by norm_num)
  · exact small_core h hz (by norm_num) (by norm_num) hS hna h8 h16 h32 h64 h128 h256 h512 h1024 h2048 _
      (fun L hLp hleaf => zleaves_skip (s := 2) hz (by norm_num) (fun k h1 h2 => by interval_cases k <;> norm_num) hLp hleaf)
      (by norm_num) (by norm_num)
  · exact small_core h hz (by norm_num) (by norm_num) hS hna h8 h16 h32 h64 h128 h256 h512 h1024 h2048 _
      (fun L hLp hleaf => zleaves_one (s := 4) (q0 := 73) hz (by norm_num) (by norm_num)
        (fun k h1 h2 hp => by
          by_cases hk : k = 1
          · subst hk
            norm_num
          · exfalso
            interval_cases k <;> first | omega | (norm_num at hp)) hLp hleaf)
      (by norm_num) (by norm_num)
  · exact small_core h hz (by norm_num) (by norm_num) hS hna h8 h16 h32 h64 h128 h256 h512 h1024 h2048 _
      (fun L hLp hleaf => zleaves_skip (s := 1) hz (by norm_num) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) hLp hleaf)
      (by norm_num) (by norm_num)
  · exact small_core h hz (by norm_num) (by norm_num) hS hna h8 h16 h32 h64 h128 h256 h512 h1024 h2048 _
      (fun L hLp hleaf => zleaves_skip (s := 1) hz (by norm_num) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) hLp hleaf)
      (by norm_num) (by norm_num)
  · exact small_core h hz (by norm_num) (by norm_num) hS hna h8 h16 h32 h64 h128 h256 h512 h1024 h2048 _
      (fun L hLp hleaf => zleaves_skip (s := 1) hz (by norm_num) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) hLp hleaf)
      (by norm_num) (by norm_num)
  · exact small_core h hz (by norm_num) (by norm_num) hS hna h8 h16 h32 h64 h128 h256 h512 h1024 h2048 _
      (fun L hLp hleaf => zleaves_skip (s := 1) hz (by norm_num) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) hLp hleaf)
      (by norm_num) (by norm_num)
  · exact small_core h hz (by norm_num) (by norm_num) hS hna h8 h16 h32 h64 h128 h256 h512 h1024 h2048 _
      (fun L hLp hleaf => zleaves_skip (s := 1) hz (by norm_num) (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) hLp hleaf)
      (by norm_num) (by norm_num)

/-- The weights argument when `3` is pinned: some simple prime `q ≥ 257` has `3 ∣ q + 1`. The weight of `3`
is `(4/3)(4098/4096)`; `7` and `31` have the weights `b7`, `b31`, which may be below the default when the
prime is not simple or has no consumer. -/
theorem pinned_master257 {m e z q : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz5 : 5 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hqP : q ∈ P) (h3q : 3 ∣ q + 1) (hq : 257 ≤ q) (b7 b31 : ℚ)
    (h7 : 1 ≤ b7 ∧ (7 ∈ P → 8 / 7 ≤ b7 ∧ b7 ≤ 4 / 3 ∧ (b7 ≠ 4 / 3 → ∀ p ∈ P, ¬ 7 ∣ p + 1)))
    (h31 : 1 ≤ b31 ∧
      (31 ∈ P → 32 / 31 ≤ b31 ∧ b31 ≤ 16 / 15 ∧ (b31 ≠ 16 / 15 → ∀ p ∈ P, ¬ 31 ∣ p + 1))) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ((4 / 3 * (258 / 256) * b7 * b31 * (64 / 63) * (2048 / 2047)) *
          ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, F3, -, -, -, -, -⟩ := facts hP hK E
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  obtain ⟨β, hβ3, hβ7, hβ31, hβ⟩ : ∃ β : ℕ → ℚ, β 3 = 4 / 3 * (258 / 256) ∧ β 7 = b7 ∧
      β 31 = b31 ∧ ∀ x : ℕ, x ≠ 3 → x ≠ 7 → x ≠ 31 → β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = 3 then 4 / 3 * (258 / 256) else if x = 7 then b7 else if x = 31 then b31
      else ((x : ℚ) + 1) / ((x : ℚ) - 1), by simp, by simp, by simp,
      fun x h1 h2 h3 => by simp [h1, h2, h3]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases h1 : p = 3
    · subst h1
      rw [hβ3]
      norm_num
    by_cases h2 : p = 7
    · subst h2
      obtain ⟨hlo, hhi, -⟩ := h7.2 hp
      rw [hβ7]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    by_cases h3 : p = 31
    · subst h3
      obtain ⟨hlo, hhi, -⟩ := h31.2 hp
      rw [hβ31]
      exact ⟨le_trans (by norm_num) hlo, le_trans hhi (by norm_num)⟩
    rw [hβ p h1 h2 h3]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → c = 3 ∨ c = 7 ∨ c = 31 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (hβ c hcon.1 hcon.2.1 hcon.2.2)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne
    rcases hsp c hne with rfl | rfl | rfl
    · have hpq : p = q := F3 3 Nat.prime_three (by norm_num) h3z p hp q hqP hd h3q
      rw [hpq, hβ q (by omega) (by omega) (by omega), hβ3]
      have hB := B_anti (a := 257) (b := q) (by norm_num) hq
      have e1 : (((257 : ℕ) : ℚ) + 1) / (((257 : ℕ) : ℚ) - 1) = 258 / 256 := by norm_num
      have e2 : (1 + 1 / ((3 : ℕ) : ℚ)) = 4 / 3 := by norm_num
      rw [e1] at hB
      rw [e2]
      exact mul_le_mul_of_nonneg_left hB (by norm_num)
    · have hne' : b7 ≠ 4 / 3 := by
        intro hb
        apply hne
        rw [hβ7, hb]
        norm_num
      exact absurd hd ((h7.2 hc).2.2 hne' p hp)
    · have hne' : b31 ≠ 16 / 15 := by
        intro hb
        apply hne
        rw [hβ31, hb]
        norm_num
      exact absurd hd ((h31.2 hc).2.2 hne' p hp)
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hd127 := hβ 127 (by norm_num) (by norm_num) (by norm_num)
  have e127 : (((127 : ℕ) : ℚ) + 1) / (((127 : ℕ) : ℚ) - 1) = 64 / 63 := by norm_num
  rw [e127] at hd127
  have hM : ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hβ31, hd127]
      exact ⟨by norm_num, h7.1, h31.1, by norm_num⟩
  rw [hβ3, hβ7, hβ31, hd127] at hM
  have hZ : ∏ x ∈ L.filter (fun x => z ∣ x + 1), β x ≤
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod (fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp hx).1)
  have hM0 : (0 : ℚ) ≤ ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x :=
    Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le
  have hZ0 : (0 : ℚ) ≤ ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le
  have hX : ∏ x ∈ L, β x ≤ (4 / 3 * (258 / 256) * b7 * b31 * (64 / 63) * (2048 / 2047)) *
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => z ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by
        have := h7.1
        have := h31.1
        positivity)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- If `m = 2 ^ k * t` with `t` odd and `m = 8 (mod 16)`, then `k = 3`. -/
theorem v2_eq_three {m k t : ℕ} (ht : Odd t) (hm : m = 2 ^ k * t) (h16 : m % 16 = 8) : k = 3 := by
  obtain ⟨s, rfl⟩ := ht
  have key := two_pow_mul_odd_mod k s
  rw [← hm] at key
  by_contra hk
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · interval_cases k
    · have h2 : m % 2 = 1 := by simpa using key
      omega
    · have h2 : m % 4 = 2 := by simpa using key
      omega
    · have h2 : m % 8 = 4 := by simpa using key
      omega
  · have h4 : 2 ^ 4 ∣ m := by
      rw [hm]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega : 4 ≤ k)) _
    norm_num at h4
    omega

/-- `z = 43` and `a = 8 (mod 16)`: no solution. The Fermat prime is `257`, a simple prime with `3 ∣ 258`, so `3`
weighs `(4/3)(258/256)`; the leaves `2 ^ k * 43 - 1` start at `k = 7`. Total at most `1.95563`. -/
theorem z43_dead {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 43) (h16 : padicValNat 2 n % 16 = 8) : False := by
  classical
  have hz : Nat.Prime 43 := by norm_num
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 43 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have he2 : 2 ≤ n.factorization 43 :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS 43).mpr rfl).2.2
  have hm0 : padicValNat 2 n ≠ 0 := by omega
  have hme : Even (padicValNat 2 n) := Nat.even_iff.mpr (by omega)
  obtain ⟨c, k, t, hc, hc2, hc3, hcm, hk, hcF, ht, hmt⟩ := exists_fermat_prime hm0 hme
  have hk3 : k = 3 := v2_eq_three ht hmt h16
  subst hk3
  have hc257 : c = 257 := (Nat.prime_dvd_prime_iff_eq hc (by norm_num)).mp (by simpa using hcF)
  subst hc257
  have hK : ∀ c : ℕ, c.Prime → c ∣ 43 ^ n.factorization 43 → c ∈ ({43} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, F2, -, -, -, -, -, -⟩ := facts hP hK E
  have hcP := F2 257 hc (by norm_num) (by simp) hcm
  have hm8 : 8 ≤ padicValNat 2 n := by omega
  obtain ⟨L, hLP, hleaf, hmain⟩ := pinned_master257 hP hz (by norm_num) E hcP (by norm_num)
    (le_refl 257) (4 / 3) (16 / 15)
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
    ⟨by norm_num, fun _ => ⟨by norm_num, le_refl _, fun h => absurd rfl h⟩⟩
  have hZ := zleaves_skip (s := 6) hz (by norm_num)
    (fun k h1 h2 => by interval_cases k <;> norm_num) (fun x hx => hP x (hLP hx)) hleaf
  refine table_close hm8 hmain (by positivity)
    (kk_le (a := 43) (b := 2) (by norm_num) (le_refl _) he2) (by norm_num)
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le) hZ ?_
  norm_num

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max 21 (max A1 (max A2 A3)),
    fun n h z hz hz7 hz2100 hS he32 c8 a6 a10 a14 a20 a28 a8 a16 a4096 U R => ?_⟩
  have he : n.factorization z % 8 = 0 := by omega
  by_cases hsmall : z < 61
  · by_cases h731 : z = 7 ∨ z = 31
    · exact (small_dead h hz h731 hS he (a8 (by omega)) (a16 (by omega) (by omega) (by omega))
        (by simpa using R 4 (by simp)) (by simpa using R 5 (by simp)) (by simpa using R 6 (by simp))
        (by simpa using R 7 (by simp)) (by simpa using R 8 (by simp)) (by simpa using R 9 (by simp))
        (by simpa using R 10 (by simp))).trans (le_max_left _ _)
    · by_cases hl8 : z ∈ ({23, 29, 37, 41, 43, 47, 53, 59} : Finset ℕ)
      · have hl8' := hl8
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl8'
        by_cases c2 : padicValNat 2 n % 4 = 2
        · by_cases hs4 : z = 29 ∨ z = 43 ∨ z = 47 ∨ z = 59
          · exact (amod4_dead_mid h hz hS he (by
              rcases hs4 with rfl | rfl | rfl | rfl
              · exact Finset.mem_insert_self 29 _
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self 43 _)
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self 47 _))
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem (Finset.mem_insert_self 59 _)))) c2).trans (le_max_left _ _)
          · have hl4s : z ∈ ({23, 37, 41, 53} : Finset ℕ) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              omega
            exact (h2 n h z hz (Or.inl hl4s) hS he32 a20 (a28 (by omega)) c2).trans
              ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
        · by_cases c16 : padicValNat 2 n % 16 = 8
          · have hz43 : z = 43 := by
              by_contra hne
              exact a16 (by omega) hne (by omega) c16
            subst hz43
            exact (z43_dead h hS c16).elim
          · exact (small8_dead h hz hl8 hS c2 (a8 (by omega)) c16
              (by simpa using R 4 (by simp)) (by simpa using R 5 (by simp))
              (by simpa using R 6 (by simp)) (by simpa using R 7 (by simp))
              (by simpa using R 8 (by simp)) (by simpa using R 9 (by simp))
              (by simpa using R 10 (by simp))).trans
              ((by norm_num : (7 : ℕ) ≤ 21).trans (le_max_left _ _))
      · have hl4 : z ∈ ({11, 13, 17, 19} : Finset ℕ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl8 ⊢
          have hz' := hz
          interval_cases z <;> first | omega | (norm_num at hz')
        exact (h1 n h z hz hl4 hS he32 a6 a10 a14 a20 a28 a8 a16 a4096 U R).trans
          ((le_max_left _ _).trans (le_max_right _ _))
  have hz61 : 61 ≤ z := by omega
  by_cases c : padicValNat 2 n % 2 = 1
  · exact (odd_bound61 h hz hz61 hS c).trans ((by norm_num : (7 : ℕ) ≤ 21).trans (le_max_left _ _))
  by_cases c4 : padicValNat 2 n % 4 = 0
  · by_cases c16 : padicValNat 2 n % 16 = 8
    · have hz257 : z = 257 := by
        by_contra hne
        exact a16 (by omega) (by omega) hne c16
      subst hz257
      exact (h3 n h hS he32 c16).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · have h0 := four_dvd_dead61 h hz hz61 (by omega) hS c4 (a8 (by omega)) c16
        (by simpa using R 4 (by simp)) (by simpa using R 5 (by simp)) (by simpa using R 6 (by simp))
        (by simpa using R 7 (by simp)) (by simpa using R 8 (by simp)) (by simpa using R 9 (by simp))
        (by simpa using R 10 (by simp))
      omega
  · have c2 : padicValNat 2 n % 4 = 2 := by omega
    by_cases hz823 : 823 ≤ z
    · exact (amod4_dead823 h hz hz823 hS he c2).trans (le_max_left _ _)
    · by_cases hl90 : z ∈ ({67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181, 191, 193, 197,
      211, 223, 227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
      317, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
      439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
      563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
      661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
      797, 809, 811, 821} : Finset ℕ)
      · exact (amod4_dead_mid h hz hS he
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem hl90)))) c2).trans (le_max_left _ _)
      · exact (h2 n h z hz (Or.inr ⟨hz61, by omega, hl90⟩) hS he32 a20 (a28 (by omega)) c2).trans
          ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1
