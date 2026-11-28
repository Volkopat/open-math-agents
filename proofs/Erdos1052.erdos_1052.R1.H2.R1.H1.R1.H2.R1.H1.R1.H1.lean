import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1
import Mathlib

-- Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H1: hypothesis H1 of reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1
-- Credit: @aroth01

/-!
# Unitary perfect numbers with odd core 5^2 and an odd exponent of 2

The step is vacuous: there is no unitary perfect number n whose only repeated odd prime is 5,
with 5^2 exactly dividing n and a = v2(n) odd, a >= 43. The hypothesis on the prime factors of a
is used only to get that 3 does not divide a.

Notation as in the parent reduction (@adammcarter): P is the set of simple odd primes of n and
  (E)  (2^a + 1) * (1 + 5^2) * prod (p + 1) = 2^(a+1) * 5^2 * prod p.

Step 1 (mod 8). For a odd, -2 = (2^((a+1)/2))^2 is a square modulo every prime divisor of
2^a + 1, so these primes are 1 or 3 mod 8. Since (2^a + 1)/3 is prime to 3 and is 3 mod 8, some
prime Q dividing 2^a + 1 is 3 mod 8 and is not 3 (`o25_exists_root_three_mod_eight`).

Step 2 (mod 3 and 5). Q is a simple prime and 3 has the single source 2^a + 1, so Q is 1 mod 3.
Then Q + 1 = 4t with t = 2 mod 3, so a prime r = 2 mod 3 divides t. If r were not 5 it would be a
simple prime with 3 dividing r + 1. Hence 5 divides Q + 1 and Q = 19 mod 120 (`o25_root_mod_120`).

Step 3. Q is not 19 (19 divides 2^a + 1 only if 9 divides a), not 139 (7 divides 140, and 7 has
the single source 13 + 1), and 259 is not prime. So Q >= 379 (`o25_root_ge_379`).

Step 4 (weights). `master_gen` of the parent reduction is applied with the weights `o25_bw`:
4/3 at 3, the chain 7 <- 13, the chain 19 <- 37 <- 73, the chain 31 <- 61, and 127; each chain is
cut at the first place where the next kept parent is forced to be large (`o25_next19` to
`o25_next127`). The leaves are Mersenne primes (`mersenne_bound`) and primes q with
q + 1 = 2^k * 5^j. Q holds one of the two factors 5 available in prod (p + 1) (`o25_ledger`) and
is not a leaf, so at most one leaf has 5 dividing q + 1; it is 19 or at least 79
(`o25_five_leaves`). The resulting bound is below 2, which contradicts `master_gen`
(`o25_final`).

The lemmas `facts`, `master_gen`, `mersenne_bound`, `setup` and the other imported lemmas are
from the parent reductions by @adammcarter.
-/

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts master_gen mersenne_bound
  two_pow_of_no_odd_prime two_pow_mul_pow_of_odd_primes_eq B_anti one_add_le_B
  three_dvd_two_pow_add_one)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (setup)

/-- A prime dividing `2 ^ a + 1` with `a` odd is `1` or `3` mod `8`, because `-2` is a square
modulo it. -/
theorem o25_prime_dvd_two_pow_odd_add_one {P a : ℕ} (hP : P.Prime) (ha : Odd a)
    (h : P ∣ 2 ^ a + 1) : P % 8 = 1 ∨ P % 8 = 3 := by
  have := Fact.mk hP
  obtain ⟨k, rfl⟩ := ha
  have hP2 : P ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ (2 * k + 1) := dvd_pow_self 2 (by omega)
    exact absurd ((Nat.dvd_add_right h2).mp h) (by norm_num)
  have hz : (2 : ZMod P) ^ (2 * k + 1) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (2 ^ (2 * k + 1) + 1) P).mpr h
    simpa using this
  have hsq : IsSquare (-2 : ZMod P) := by
    refine ⟨(2 : ZMod P) ^ (k + 1), ?_⟩
    linear_combination (-2 : ZMod P) * hz
  exact (ZMod.exists_sq_eq_neg_two_iff hP2).mp hsq

/-- A product of numbers that are `1` mod `8` is `1` mod `8`. -/
theorem o25_list_prod_mod_eight_eq_one : ∀ l : List ℕ, (∀ p ∈ l, p % 8 = 1) → l.prod % 8 = 1
  | [], _ => by simp
  | p :: l, h => by
    have hp := h p (by simp)
    have hl := o25_list_prod_mod_eight_eq_one l (fun q hq => h q (by simp [hq]))
    rw [List.prod_cons, Nat.mul_mod, hp, hl]

/-- If `n` is `3` mod `8` and all its prime factors are `1` or `3` mod `8`, one of them is `3`. -/
theorem o25_exists_prime_three_mod_eight {n : ℕ} (hn : n % 8 = 3)
    (h : ∀ p, p.Prime → p ∣ n → p % 8 = 1 ∨ p % 8 = 3) : ∃ p, p.Prime ∧ p ∣ n ∧ p % 8 = 3 := by
  by_contra hcon
  push Not at hcon
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have key := o25_list_prod_mod_eight_eq_one n.primeFactorsList (fun p hp => by
    have hpp := Nat.prime_of_mem_primeFactorsList hp
    have hd := Nat.dvd_of_mem_primeFactorsList hp
    rcases h p hpp hd with h1 | h3
    · exact h1
    · exact absurd h3 (hcon p hpp hd))
  rw [Nat.prod_primeFactorsList hn0] at key
  omega

/-- `9 ∣ 2 ^ a + 1` forces `3 ∣ a`. -/
theorem o25_not_nine_dvd_two_pow_add_one {a : ℕ} (h3 : ¬ 3 ∣ a) : ¬ 9 ∣ 2 ^ a + 1 := by
  intro h
  have key : (2 ^ a) % 9 = (2 ^ (a % 6)) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod a 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h9 : (2 ^ a + 1) % 9 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.add_mod, key] at h9
  have hlt : a % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : a % 6 <;> first | (norm_num at h9; done) | omega

/-- Step 1 of the argument for Erdős 1052 with `a` odd: if `a ≥ 3` is odd and `3 ∤ a`, then
`2 ^ a + 1` has a prime factor `P ≠ 3` with `P % 8 = 3`. -/
theorem o25_exists_root_three_mod_eight {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) (h3 : ¬ 3 ∣ a) :
    ∃ P, P.Prime ∧ P ∣ 2 ^ a + 1 ∧ P ≠ 3 ∧ P % 8 = 3 := by
  have hmod3 : ∀ k : ℕ, 2 ^ (2 * k + 1) % 3 = 2 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num]
      omega
  have hdiv : 3 ∣ 2 ^ a + 1 := by
    obtain ⟨k, rfl⟩ := ha
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, hmod3 k]
  obtain ⟨M, hM⟩ := hdiv
  have h8 : (2 ^ a + 1) % 8 = 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, a = j + 3 := ⟨a - 3, by omega⟩
    rw [pow_add, show (2 : ℕ) ^ 3 = 8 by norm_num]
    omega
  have hM8 : M % 8 = 3 := by omega
  have hM3 : ¬ 3 ∣ M := by
    rintro ⟨t, rfl⟩
    exact o25_not_nine_dvd_two_pow_add_one h3 ⟨t, by rw [hM]; ring⟩
  obtain ⟨P, hP, hPM, hP8⟩ := o25_exists_prime_three_mod_eight hM8 (fun p hp hd => by
    have hd' : p ∣ 2 ^ a + 1 := by rw [hM]; exact Dvd.dvd.mul_left hd 3
    exact o25_prime_dvd_two_pow_odd_add_one hp ha hd')
  refine ⟨P, hP, by rw [hM]; exact Dvd.dvd.mul_left hPM 3, ?_, hP8⟩
  rintro rfl
  exact hM3 hPM


/-- The product of a finset of distinct primes is not divisible by the square of any prime. -/
lemma o25_not_sq_dvd_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℕ} (hq : q.Prime) :
    ¬ q ^ 2 ∣ ∏ p ∈ S, p := by
  classical
  intro h
  by_cases hqS : q ∈ S
  · rw [← Finset.mul_prod_erase S (fun p => p) hqS] at h
    have h' : q ∣ ∏ p ∈ S.erase q, p := by
      have : q * q ∣ q * ∏ p ∈ S.erase q, p := by simpa [pow_two] using h
      exact (Nat.mul_dvd_mul_iff_left hq.pos).mp this
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h'
    exact (Finset.ne_of_mem_erase hp)
      ((Nat.prime_dvd_prime_iff_eq hq (hS p (Finset.mem_of_mem_erase hp))).mp hqp).symm
  · obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp
      ((dvd_pow_self q two_ne_zero).trans h)
    exact hqS (((Nat.prime_dvd_prime_iff_eq hq (hS p hp)).mp hqp) ▸ hp)

/-- An odd prime other than `5` dividing the left side of (E) is a simple prime. -/
theorem o25_prime_dvd_lhs_mem {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr5 : r ≠ 5)
    (hd : r ∣ (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1)) : r ∈ P := by
  rw [E] at hd
  rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)) hr2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp (hr.dvd_of_dvd_pow h)) hr5
  · obtain ⟨p, hp, hrp⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp h
    rwa [(Nat.prime_dvd_prime_iff_eq hr (hP p hp).1).mp hrp]

/-- `3` has a single source: if `3 ∣ 2 ^ m + 1`, no simple prime `q` has `3 ∣ q + 1`. -/
theorem o25_no_three_dvd_succ {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (h3 : 3 ∣ 2 ^ m + 1) {q : ℕ} (hq : q ∈ P) : ¬ 3 ∣ q + 1 := by
  intro hq3
  have h1 : 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ P, (p + 1) := by
    rw [pow_two]
    exact Nat.mul_dvd_mul h3 (hq3.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hq))
  have h9 : 3 ^ 2 ∣ 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p := by
    rw [← E, show (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1)
      = ((2 ^ m + 1) * ∏ p ∈ P, (p + 1)) * (1 + 5 ^ 2) by ring]
    exact h1.mul_right _
  have hcop : Nat.Coprime (3 ^ 2) (2 ^ (m + 1) * 5 ^ 2) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.pow_right _ (by norm_num)
    · exact Nat.Coprime.pow_right _ (by norm_num)
  exact o25_not_sq_dvd_prod_primes (fun p hp => (hP p hp).1) Nat.prime_three
    (hcop.dvd_of_dvd_mul_left h9)

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

/-- Steps 1 and 2: for `m` odd, `m ≥ 3`, `3 ∤ m`, equation (E) forces a simple prime `Q`
dividing `2 ^ m + 1` with `Q ≡ 19 (mod 120)`; in particular `5 ∣ Q + 1`. -/
theorem o25_root_mod_120 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : Odd m) (hm3 : 3 ≤ m) (h3 : ¬ 3 ∣ m) :
    ∃ Q ∈ P, Q ∣ 2 ^ m + 1 ∧ Q % 120 = 19 := by
  obtain ⟨Q, hQ, hQd, hQ3, hQ8⟩ := o25_exists_root_three_mod_eight hm hm3 h3
  have h3d : 3 ∣ 2 ^ m + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hm
  have hQP : Q ∈ P :=
    o25_prime_dvd_lhs_mem hP E hQ (by omega) (by omega) ((hQd.mul_right _).mul_right _)
  have hQ1 : Q % 3 = 1 := by
    have hns := o25_no_three_dvd_succ hP E h3d hQP
    have hQ0 : Q % 3 ≠ 0 := by
      intro h0
      exact hQ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hQ).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
    omega
  obtain ⟨t, ht⟩ : ∃ t, Q + 1 = 4 * t := ⟨(Q + 1) / 4, by omega⟩
  have ht3 : t % 3 = 2 := by omega
  have htodd : t % 2 = 1 := by omega
  obtain ⟨r, hr, hrt, hr3⟩ := o25_exists_prime_two_mod_three ht3
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  have hr5 : r = 5 := by
    by_contra h5
    have hrQ : r ∣ Q + 1 := hrt.trans ⟨4, by rw [ht]; ring⟩
    have hrl : r ∣ (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) :=
      Dvd.dvd.mul_left (hrQ.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hQP)) _
    have hrP : r ∈ P := o25_prime_dvd_lhs_mem hP E hr hr2 h5 hrl
    exact o25_no_three_dvd_succ hP E h3d hrP (by omega)
  subst hr5
  refine ⟨Q, hQP, hQd, ?_⟩
  obtain ⟨s, rfl⟩ := hrt
  omega


/-- `19 ∣ 2 ^ m + 1` forces `m ≡ 9 (mod 18)`, hence `3 ∣ m`. -/
theorem o25_three_dvd_of_nineteen_dvd {m : ℕ} (h : 19 ∣ 2 ^ m + 1) : 3 ∣ m := by
  have key : (2 ^ m) % 19 = (2 ^ (m % 18)) % 19 := by
    conv_lhs => rw [← Nat.div_add_mod m 18, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h19 : (2 ^ m + 1) % 19 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.add_mod, key] at h19
  have hlt : m % 18 < 18 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : m % 18 <;> first | (norm_num at h19; done) | omega

/-- Steps 1 to 3 (first half): the root `Q ≡ 19 (mod 120)` is not `19`, so `Q ≥ 139`. -/
theorem o25_root_ge_139 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : Odd m) (hm3 : 3 ≤ m) (h3 : ¬ 3 ∣ m) :
    ∃ Q ∈ P, Q ∣ 2 ^ m + 1 ∧ Q % 120 = 19 ∧ 139 ≤ Q := by
  obtain ⟨Q, hQP, hQd, hQ120⟩ := o25_root_mod_120 hP E hm hm3 h3
  have hQ19 : Q ≠ 19 := by
    rintro rfl
    exact h3 (o25_three_dvd_of_nineteen_dvd hQd)
  exact ⟨Q, hQP, hQd, hQ120, by omega⟩


/-- `13` is a simple prime: it divides `1 + 5 ^ 2`. -/
theorem o25_thirteen_mem {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p) :
    13 ∈ P :=
  o25_prime_dvd_lhs_mem hP E (by norm_num) (by norm_num) (by norm_num)
    (Dvd.dvd.mul_right (Dvd.dvd.mul_left (by norm_num : 13 ∣ 1 + 5 ^ 2) _) _)

/-- `7` has a single source, `13 + 1`: no other simple prime `q` has `7 ∣ q + 1`. -/
theorem o25_no_seven_dvd_succ {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {q : ℕ} (hq : q ∈ P) (hq13 : q ≠ 13) : ¬ 7 ∣ q + 1 := by
  classical
  intro h7
  have h13 := o25_thirteen_mem hP E
  have hprod : (13 + 1) * (q + 1) ∣ ∏ p ∈ P, (p + 1) := by
    rw [← Finset.mul_prod_erase P (fun p => p + 1) h13]
    exact Nat.mul_dvd_mul_left _
      (Finset.dvd_prod_of_mem (fun p => p + 1) (Finset.mem_erase.mpr ⟨hq13, hq⟩))
  have h49 : 7 ^ 2 ∣ ∏ p ∈ P, (p + 1) := by
    have h77 : 7 * 7 ∣ (13 + 1) * (q + 1) := Nat.mul_dvd_mul (by norm_num) h7
    rw [pow_two]
    exact h77.trans hprod
  have h49' : 7 ^ 2 ∣ 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p := by
    rw [← E]
    exact Dvd.dvd.mul_left h49 _
  have hcop : Nat.Coprime (7 ^ 2) (2 ^ (m + 1) * 5 ^ 2) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.pow_right _ (by norm_num)
    · exact Nat.Coprime.pow_right _ (by norm_num)
  exact o25_not_sq_dvd_prod_primes (fun p hp => (hP p hp).1) (by norm_num)
    (hcop.dvd_of_dvd_mul_left h49')

/-- Steps 1 to 3: for `m` odd, `m ≥ 3`, `3 ∤ m`, equation (E) forces a simple prime `Q` with
`Q ∣ 2 ^ m + 1`, `Q ≡ 19 (mod 120)` and `Q ≥ 379`. -/
theorem o25_root_ge_379 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : Odd m) (hm3 : 3 ≤ m) (h3 : ¬ 3 ∣ m) :
    ∃ Q ∈ P, Q ∣ 2 ^ m + 1 ∧ Q % 120 = 19 ∧ 379 ≤ Q := by
  obtain ⟨Q, hQP, hQd, hQ120, hQ139⟩ := o25_root_ge_139 hP E hm hm3 h3
  have hQprime := (hP Q hQP).1
  have h139 : Q ≠ 139 := by
    rintro rfl
    exact o25_no_seven_dvd_succ hP E hQP (by norm_num) (by norm_num)
  have h259 : Q ≠ 259 := by
    rintro rfl
    exact absurd hQprime (by norm_num)
  exact ⟨Q, hQP, hQd, hQ120, by omega⟩

/-- Prime divisors of the core `5 ^ 2`. -/
theorem o25_hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ 2 → c ∈ ({5} : Finset ℕ) := fun c hc hd =>
  Finset.mem_singleton.mpr
    ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_five).mp (hc.dvd_of_dvd_pow hd))

/-- The weights. Along a kept edge `p -> c` (`c` the least odd prime factor of `p + 1` other
than `5`) they satisfy `(1 + 1 / c) * w p ≤ w c`; elsewhere `w x = (x + 1) / (x - 1)`. -/
def o25_bw (x : ℕ) : ℚ :=
  if x = 3 then 4 / 3
  else if x = 7 then 16 / 13
  else if x = 13 then 14 / 13
  else if x = 19 then 800 / 729
  else if x = 37 then 760 / 729
  else if x = 73 then 740 / 729
  else if x = 31 then 256 / 243
  else if x = 61 then 248 / 243
  else if x = 127 then 1280 / 1269
  else ((x : ℚ) + 1) / ((x : ℚ) - 1)

theorem o25_bw_of_ne {x : ℕ} (h1 : x ≠ 3) (h2 : x ≠ 7) (h3 : x ≠ 13) (h4 : x ≠ 19) (h5 : x ≠ 37)
    (h6 : x ≠ 73) (h7 : x ≠ 31) (h8 : x ≠ 61) (h9 : x ≠ 127) :
    o25_bw x = ((x : ℚ) + 1) / ((x : ℚ) - 1) := by
  unfold o25_bw
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
    if_neg h9]

theorem o25_bw_big {x : ℕ} (h : 127 < x) : o25_bw x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
  o25_bw_of_ne (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem o25_bw_special {x : ℕ} (h : o25_bw x ≠ ((x : ℚ) + 1) / ((x : ℚ) - 1)) :
    x = 3 ∨ x = 7 ∨ x = 13 ∨ x = 19 ∨ x = 37 ∨ x = 73 ∨ x = 31 ∨ x = 61 ∨ x = 127 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hcon
  exact h (o25_bw_of_ne h1 h2 h3 h4 h5 h6 h7 h8 h9)

theorem o25_bw_bounds {p : ℕ} (hp : 2 ≤ p) :
    1 + 1 / (p : ℚ) ≤ o25_bw p ∧ o25_bw p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  by_cases h : o25_bw p = ((p : ℚ) + 1) / ((p : ℚ) - 1)
  · rw [h]
    exact ⟨one_add_le_B hp, le_refl _⟩
  · rcases o25_bw_special h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [o25_bw]

/-- A kept parent beyond `T > 127` carries the default weight, bounded by its value at `T`. -/
theorem o25_step_big {c T p : ℕ} (hT : 127 < T) (hTp : T ≤ p)
    (hnum : (1 + 1 / (c : ℚ)) * (((T : ℚ) + 1) / ((T : ℚ) - 1)) ≤ o25_bw c) :
    (1 + 1 / (c : ℚ)) * o25_bw p ≤ o25_bw c := by
  rw [o25_bw_big (by omega)]
  exact (mul_le_mul_of_nonneg_left (B_anti (by omega) hTp) (by positivity)).trans hnum

/-- The kept parents of `19`: `37`, or at least `151`. -/
theorem o25_next19 {p : ℕ} (hp : p.Prime) (hd : 19 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 19 ≤ c') :
    p = 37 ∨ 151 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 19 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `37`: `73`, or at least `739`. -/
theorem o25_next37 {p : ℕ} (hp : p.Prime) (hd : 37 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 37 ≤ c') :
    p = 73 ∨ 739 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 37 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `73` are at least `1459`. -/
theorem o25_next73 {p : ℕ} (hp : p.Prime) (hd : 73 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 73 ≤ c') :
    1459 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 73 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `31`: `61`, or at least `619`. -/
theorem o25_next31 {p : ℕ} (hp : p.Prime) (hd : 31 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 31 ≤ c') :
    p = 61 ∨ 619 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 31 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `61` are at least `487`. -/
theorem o25_next61 {p : ℕ} (hp : p.Prime) (hd : 61 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 61 ≤ c') :
    487 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 61 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `127` are at least `2539`. -/
theorem o25_next127 {p : ℕ} (hp : p.Prime) (hd : 127 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    2539 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 127 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The weights are consistent along kept edges. -/
theorem o25_h4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : m % 2 = 1) :
    ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      o25_bw c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * o25_bw p ≤ o25_bw c := by
  intro p hp c hc hd hl hne
  obtain ⟨-, -, F3, F4, -, -, F7, F8⟩ := facts hP o25_hK E
  have hpp := (hP p hp).1
  rcases o25_bw_special hne with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hd
      (F4 3 (by norm_num) (by norm_num) (by simp) (three_dvd_two_pow_add_one hm) p hp)
  · have h13 : 13 ∈ P := F7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
    obtain rfl : p = 13 :=
      F3 7 (by norm_num) (by norm_num) (by simp) p hp 13 h13 hd (by norm_num)
    norm_num [o25_bw]
  · exact absurd hd (F8 13 (by norm_num) (by norm_num) (by simp) (by norm_num) p hp)
  · rcases o25_next19 hpp hd hl with rfl | h
    · norm_num [o25_bw]
    · exact o25_step_big (T := 151) (by norm_num) h (by norm_num [o25_bw])
  · rcases o25_next37 hpp hd hl with rfl | h
    · norm_num [o25_bw]
    · exact o25_step_big (T := 739) (by norm_num) h (by norm_num [o25_bw])
  · exact o25_step_big (T := 1459) (by norm_num) (o25_next73 hpp hd hl) (by norm_num [o25_bw])
  · rcases o25_next31 hpp hd hl with rfl | h
    · norm_num [o25_bw]
    · exact o25_step_big (T := 619) (by norm_num) h (by norm_num [o25_bw])
  · exact o25_step_big (T := 487) (by norm_num) (o25_next61 hpp hd hl) (by norm_num [o25_bw])
  · exact o25_step_big (T := 2539) (by norm_num) (o25_next127 hpp hd hl) (by norm_num [o25_bw])

/-- The ledger of `5`: the numbers `p + 1`, `p` in a subset of `P`, hold at most two factors
`5` between them. -/
theorem o25_ledger {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {T : Finset ℕ} (hT : T ⊆ P) : ¬ 5 ^ 3 ∣ ∏ p ∈ T, (p + 1) := by
  intro h
  have h1 : 5 ^ 3 ∣ ∏ p ∈ P, (p + 1) :=
    h.trans (Finset.prod_dvd_prod_of_subset _ _ (fun x => x + 1) hT)
  have h2 : 5 ^ 3 ∣ 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p := by
    rw [← E]
    exact Dvd.dvd.mul_left h1 _
  have h3 : 5 ^ 2 * 5 ∣ 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
    have e : 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p = 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
    rw [← e]
    exact h2
  have h4 : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h4 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  · obtain ⟨p, hp, h5p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_five.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five (hP p hp).1).mp h5p
    exact h5 (this ▸ hp)

/-- The leaves with `5 ∣ q + 1` weigh at most `w 19` in total: the root `Q` holds one factor `5`
and is not a leaf, so there is at most one such leaf, it has `q + 1 = 2 ^ k * 5`, and it is `19`
or at least `79`. -/
theorem o25_five_leaves {m : ℕ} {P L : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hLP : L ⊆ P) (hleaf : ∀ q ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5)
    {Q : ℕ} (hQP : Q ∈ P) (hQ120 : Q % 120 = 19) (hQ379 : 379 ≤ Q) :
    ∏ q ∈ L.filter (fun q => 5 ∣ q + 1), o25_bw q ≤ 800 / 729 := by
  classical
  have hmem : ∀ q ∈ L.filter (fun q => 5 ∣ q + 1), q ∈ L ∧ 5 ∣ q + 1 :=
    fun q hq => Finset.mem_filter.mp hq
  have hQ5 : 5 ∣ Q + 1 := by omega
  have hQL : Q ∉ L.filter (fun q => 5 ∣ q + 1) := by
    intro hQ
    obtain ⟨hQL, -⟩ := hmem Q hQ
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := Q + 1) (z := 5) (by omega)
      (hleaf Q hQL)
    by_cases hj : 3 ≤ j
    · apply o25_ledger hP h5 E (T := {Q}) (Finset.singleton_subset_iff.mpr hQP)
      rw [Finset.prod_singleton, hkj]
      exact Dvd.dvd.mul_left (pow_dvd_pow 5 hj) _
    · by_cases hk : 3 ≤ k
      · have h8 : 2 ^ 3 ∣ Q + 1 := by
          rw [hkj]
          exact Dvd.dvd.mul_right (pow_dvd_pow 2 hk) _
        norm_num at h8
        omega
      · have hj' : j < 3 := by omega
        have hk' : k < 3 := by omega
        interval_cases j <;> interval_cases k <;> norm_num at hkj <;> omega
  have huniq : ∀ a ∈ L.filter (fun q => 5 ∣ q + 1), ∀ b ∈ L.filter (fun q => 5 ∣ q + 1),
      a = b := by
    intro a ha b hb
    by_contra hab
    obtain ⟨haL, ha5⟩ := hmem a ha
    obtain ⟨hbL, hb5⟩ := hmem b hb
    have haQ : Q ≠ a := fun h => hQL (h ▸ ha)
    have hbQ : Q ≠ b := fun h => hQL (h ▸ hb)
    have hsub : ({Q, a, b} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · rw [h]; exact hQP
      · rw [h]; exact hLP haL
      · rw [h]; exact hLP hbL
    apply o25_ledger hP h5 E hsub
    rw [Finset.prod_insert (by simp [haQ, hbQ]), Finset.prod_pair hab,
      show (5 : ℕ) ^ 3 = 5 * (5 * 5) by norm_num]
    exact mul_dvd_mul hQ5 (mul_dvd_mul ha5 hb5)
  have hval : ∀ q ∈ L.filter (fun q => 5 ∣ q + 1), o25_bw q ≤ 800 / 729 := by
    intro q hq
    obtain ⟨hqL, hq5⟩ := hmem q hq
    have hqQ : Q ≠ q := fun h => hQL (h ▸ hq)
    have hqP := hLP hqL
    have hqp := (hP q hqP).1
    have h25 : ¬ 25 ∣ q + 1 := by
      intro h25
      have hsub : ({Q, q} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h
        · rw [h]; exact hQP
        · rw [h]; exact hqP
      apply o25_ledger hP h5 E hsub
      rw [Finset.prod_pair hqQ, show (5 : ℕ) ^ 3 = 5 * 25 by norm_num]
      exact mul_dvd_mul hQ5 h25
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := q + 1) (z := 5) (by omega)
      (hleaf q hqL)
    have hj1 : j = 1 := by
      rcases Nat.lt_or_ge j 2 with hj | hj
      · interval_cases j
        · exfalso
          rw [hkj, pow_zero, mul_one] at hq5
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
            (Nat.prime_five.dvd_of_dvd_pow hq5)
          omega
        · rfl
      · exfalso
        apply h25
        rw [hkj, show (25 : ℕ) = 5 ^ 2 by norm_num]
        exact Dvd.dvd.mul_left (pow_dvd_pow 5 hj) _
    subst hj1
    rw [pow_one] at hkj
    by_cases hk : k < 4
    · have hq4 : q = 4 ∨ q = 9 ∨ q = 19 ∨ q = 39 := by
        interval_cases k <;> norm_num at hkj <;> omega
      rcases hq4 with rfl | rfl | rfl | rfl
      · exact absurd hqp (by norm_num)
      · exact absurd hqp (by norm_num)
      · norm_num [o25_bw]
      · exact absurd hqp (by norm_num)
    · have h16 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h79 : 79 ≤ q := by
        norm_num at h16
        omega
      exact (o25_bw_bounds hqp.two_le).2.trans ((B_anti (by norm_num) h79).trans (by norm_num))
  rcases Finset.eq_empty_or_nonempty (L.filter (fun q => 5 ∣ q + 1)) with h0 | ⟨q, hq⟩
  · rw [h0, Finset.prod_empty]
    norm_num
  · have hs : L.filter (fun q => 5 ∣ q + 1) = {q} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hq, fun x hx => huniq x hx q hq⟩
    rw [hs, Finset.prod_singleton]
    exact hval q hq

/-- Step 4 and the conclusion: equation (E) has no solution with `m` odd, `m ≥ 43`, `3 ∤ m`. -/
theorem o25_final {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : m % 2 = 1) (hm43 : 43 ≤ m) (h3 : ¬ 3 ∣ m) : False := by
  classical
  obtain ⟨Q, hQP, -, hQ120, hQ379⟩ := o25_root_ge_379 hP E (Nat.odd_iff.mpr hm) (by omega) h3
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP o25_hK (by norm_num) E o25_bw
    (fun p hp => o25_bw_bounds (hP p hp).1.two_le) (o25_h4 hP E hm)
  have hleaf : ∀ q ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5 := fun q hq c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf q hq c hc h2 hd)
  have hpos : ∀ q ∈ L, 0 < o25_bw q := fun q hq =>
    lt_of_lt_of_le (by positivity) (o25_bw_bounds (hP q (hLP hq)).1.two_le).1
  have h5part := o25_five_leaves hP h5 E hLP hleaf hQP hQ120 hQ379
  have hMpart : ∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), o25_bw q ≤
      (o25_bw 3 * o25_bw 7 * o25_bw 31 * o25_bw 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro q hq
      exact (hP q (hLP (Finset.mem_filter.mp hq).1)).1
    · intro q hq
      obtain ⟨hqL, hq5⟩ := Finset.mem_filter.mp hq
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hq5 (hleaf q hqL c hc h2 hd ▸ hd))
    · intro q hq
      have hqL := (Finset.mem_filter.mp hq).1
      exact ⟨hpos q hqL, (o25_bw_bounds (hP q (hLP hqL)).1.two_le).2⟩
    · norm_num [o25_bw]
  have hM0 : (0 : ℚ) ≤ ∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), o25_bw q :=
    Finset.prod_nonneg fun q hq => (hpos q (Finset.mem_filter.mp hq).1).le
  have hX : (∏ q ∈ L.filter (fun q => 5 ∣ q + 1), o25_bw q) *
      (∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), o25_bw q) ≤
      (800 / 729) * ((o25_bw 3 * o25_bw 7 * o25_bw 31 * o25_bw 127) * (2048 / 2047)) :=
    mul_le_mul h5part hMpart hM0 (by norm_num)
  rw [Finset.prod_filter_mul_prod_filter_not L (fun q => 5 ∣ q + 1) o25_bw] at hX
  have hX0 : (0 : ℚ) ≤ ∏ q ∈ L, o25_bw q := Finset.prod_nonneg fun q hq => (hpos q hq).le
  have hpow : (1 : ℚ) / 2 ^ m ≤ 1 / 2 ^ 43 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hm43)
  have hKK : (((1 + 5 ^ 2 : ℕ) : ℚ) / ((5 ^ 2 : ℕ) : ℚ)) = 26 / 25 := by norm_num
  rw [hKK] at hmain
  have h1 : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) * ∏ q ∈ L, o25_bw q ≤
      (1 + 1 / 2 ^ 43) * (26 / 25) *
        ((800 / 729) * ((o25_bw 3 * o25_bw 7 * o25_bw 31 * o25_bw 127) * (2048 / 2047))) := by
    apply mul_le_mul _ hX hX0 (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith
  have h2 : (1 + 1 / (2 : ℚ) ^ 43) * (26 / 25) *
      ((800 / 729) * ((o25_bw 3 * o25_bw 7 * o25_bw 31 * o25_bw 127) * (2048 / 2047))) < 2 := by
    norm_num [o25_bw]
  linarith

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1.H1 := by
  refine ⟨0, fun n h hS he h43 hodd hd => ?_⟩
  exfalso
  obtain ⟨hP, h5, E⟩ := setup h hS
  rw [he] at E
  have h3 : ¬ 3 ∣ padicValNat 2 n := fun h3 => by
    have := (hd 3 Nat.prime_three h3).1
    omega
  exact o25_final hP h5 E hodd h43 h3
