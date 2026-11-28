import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H2.R1
-- Credit: @adammcarter
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1 (3 the only repeated odd
-- prime, exponent e of 3 equal to 577 or 764) by ruling out e = 577 and splitting e = 764 by the
-- parity of a = padicValNat 2 n.  Proving the two H proves the step.
--
-- PROVED BELOW: e = 577 is impossible (kill3_e577, in fact for every odd multiple of 577).  The
-- 275-digit prime factor of (3^577 + 1)/4 is a simple prime of n, and the odd primes of p + 1 for a
-- simple prime p are again simple primes; the chains recorded in kill3_e577 reach two different
-- simple primes p, p' with 11 dividing both p + 1 and p' + 1, so 11 has two sources in the balance
-- equation (2^a + 1)(3^e + 1) prod (p + 1) = 2^(a+1) 3^e prod p.  Witness primes above 4.3 * 10^7
-- are certified by the Lucas test (p - 1 factorizations from factordb, GMP-ECM and PARI, re-checked).
--
-- H1 (OPEN): e = 764, a odd, a no odd multiple of DA.
-- H2 (OPEN): e = 764, a even, a no odd multiple of DA.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1 hiding H1 H2 main

-- H1: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 equal to 764, a odd, and a no odd multiple of any d in DA.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 764 →
    padicValNat 2 n % 2 = 1 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: the same with a even.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 764 →
    padicValNat 2 n % 2 = 0 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

theorem prime_3953908627 : Nat.Prime 3953908627 := by
  refine lucas_primality 3953908627 (2 : ZMod 3953908627) ?_ (fun q hq hd => ?_)
  · rw [show 3953908627 - 1 = 3953908626 from by norm_num]
    reduce_mod_char
  · have e : 3953908627 - 1 = [2 ^ 1, 3 ^ 1, 19 ^ 1, 34683409 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3953908627 - 1) / 2 = 1976954313 from by norm_num]
      have h2 : (2 : ZMod 3953908627) ^ 1976954313 = ((3953908626 : ℕ) : ZMod 3953908627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3953908627 - 1) / 3 = 1317969542 from by norm_num]
      have h2 : (2 : ZMod 3953908627) ^ 1317969542 = ((3157266596 : ℕ) : ZMod 3953908627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3953908627 - 1) / 19 = 208100454 from by norm_num]
      have h2 : (2 : ZMod 3953908627) ^ 208100454 = ((137883596 : ℕ) : ZMod 3953908627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3953908627 - 1) / 34683409 = 114 from by norm_num]
      have h2 : (2 : ZMod 3953908627) ^ 114 = ((3289640214 : ℕ) : ZMod 3953908627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3629688119587 : Nat.Prime 3629688119587 := by
  refine lucas_primality 3629688119587 (2 : ZMod 3629688119587) ?_ (fun q hq hd => ?_)
  · rw [show 3629688119587 - 1 = 3629688119586 from by norm_num]
    reduce_mod_char
  · have e : 3629688119587 - 1 = [2 ^ 1, 3 ^ 3, 17 ^ 1, 3953908627 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3629688119587 - 1) / 2 = 1814844059793 from by norm_num]
      have h2 : (2 : ZMod 3629688119587) ^ 1814844059793 = ((3629688119586 : ℕ) : ZMod 3629688119587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3629688119587 - 1) / 3 = 1209896039862 from by norm_num]
      have h2 : (2 : ZMod 3629688119587) ^ 1209896039862 = ((2266976922878 : ℕ) : ZMod 3629688119587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3629688119587 - 1) / 17 = 213511065858 from by norm_num]
      have h2 : (2 : ZMod 3629688119587) ^ 213511065858 = ((1140884129183 : ℕ) : ZMod 3629688119587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3953908627).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3629688119587 - 1) / 3953908627 = 918 from by norm_num]
      have h2 : (2 : ZMod 3629688119587) ^ 918 = ((2625087207663 : ℕ) : ZMod 3629688119587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3810279622288931599 : Nat.Prime 3810279622288931599 := by
  refine lucas_primality 3810279622288931599 (6 : ZMod 3810279622288931599) ?_ (fun q hq hd => ?_)
  · rw [show 3810279622288931599 - 1 = 3810279622288931598 from by norm_num]
    reduce_mod_char
  · have e : 3810279622288931599 - 1 = [2 ^ 1, 3 ^ 1, 174959 ^ 1, 3629688119587 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3810279622288931599 - 1) / 2 = 1905139811144465799 from by norm_num]
      have h2 : (6 : ZMod 3810279622288931599) ^ 1905139811144465799 = ((3810279622288931598 : ℕ) : ZMod 3810279622288931599) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3810279622288931599 - 1) / 3 = 1270093207429643866 from by norm_num]
      have h2 : (6 : ZMod 3810279622288931599) ^ 1270093207429643866 = ((2108573045988602280 : ℕ) : ZMod 3810279622288931599) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3810279622288931599 - 1) / 174959 = 21778128717522 from by norm_num]
      have h2 : (6 : ZMod 3810279622288931599) ^ 21778128717522 = ((1462505276891666720 : ℕ) : ZMod 3810279622288931599) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3629688119587).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3810279622288931599 - 1) / 3629688119587 = 1049754 from by norm_num]
      have h2 : (6 : ZMod 3810279622288931599) ^ 1049754 = ((538183721433983351 : ℕ) : ZMod 3810279622288931599) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_185901652872784317405136897 : Nat.Prime 185901652872784317405136897 := by
  refine lucas_primality 185901652872784317405136897 (13 : ZMod 185901652872784317405136897) ?_ (fun q hq hd => ?_)
  · rw [show 185901652872784317405136897 - 1 = 185901652872784317405136896 from by norm_num]
    reduce_mod_char
  · have e : 185901652872784317405136897 - 1 = [2 ^ 11, 3 ^ 2, 2647 ^ 1, 3810279622288931599 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185901652872784317405136897 - 1) / 2 = 92950826436392158702568448 from by norm_num]
      have h2 : (13 : ZMod 185901652872784317405136897) ^ 92950826436392158702568448 = ((185901652872784317405136896 : ℕ) : ZMod 185901652872784317405136897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185901652872784317405136897 - 1) / 3 = 61967217624261439135045632 from by norm_num]
      have h2 : (13 : ZMod 185901652872784317405136897) ^ 61967217624261439135045632 = ((152967769484743066862443262 : ℕ) : ZMod 185901652872784317405136897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185901652872784317405136897 - 1) / 2647 = 70231073998029587232768 from by norm_num]
      have h2 : (13 : ZMod 185901652872784317405136897) ^ 70231073998029587232768 = ((18927393150268276361439333 : ℕ) : ZMod 185901652872784317405136897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3810279622288931599).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185901652872784317405136897 - 1) / 3810279622288931599 = 48789504 from by norm_num]
      have h2 : (13 : ZMod 185901652872784317405136897) ^ 48789504 = ((86523542479535550443669515 : ℕ) : ZMod 185901652872784317405136897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3700679913173 : Nat.Prime 3700679913173 := by
  refine lucas_primality 3700679913173 (2 : ZMod 3700679913173) ?_ (fun q hq hd => ?_)
  · rw [show 3700679913173 - 1 = 3700679913172 from by norm_num]
    reduce_mod_char
  · have e : 3700679913173 - 1 = [2 ^ 2, 11 ^ 1, 17 ^ 1, 5399 ^ 1, 916361 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3700679913173 - 1) / 2 = 1850339956586 from by norm_num]
      have h2 : (2 : ZMod 3700679913173) ^ 1850339956586 = ((3700679913172 : ℕ) : ZMod 3700679913173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3700679913173 - 1) / 11 = 336425446652 from by norm_num]
      have h2 : (2 : ZMod 3700679913173) ^ 336425446652 = ((866585328135 : ℕ) : ZMod 3700679913173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3700679913173 - 1) / 17 = 217687053716 from by norm_num]
      have h2 : (2 : ZMod 3700679913173) ^ 217687053716 = ((3485190194687 : ℕ) : ZMod 3700679913173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3700679913173 - 1) / 5399 = 685438028 from by norm_num]
      have h2 : (2 : ZMod 3700679913173) ^ 685438028 = ((2738712471610 : ℕ) : ZMod 3700679913173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3700679913173 - 1) / 916361 = 4038452 from by norm_num]
      have h2 : (2 : ZMod 3700679913173) ^ 4038452 = ((586511606450 : ℕ) : ZMod 3700679913173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2205605228251109 : Nat.Prime 2205605228251109 := by
  refine lucas_primality 2205605228251109 (2 : ZMod 2205605228251109) ?_ (fun q hq hd => ?_)
  · rw [show 2205605228251109 - 1 = 2205605228251108 from by norm_num]
    reduce_mod_char
  · have e : 2205605228251109 - 1 = [2 ^ 2, 149 ^ 1, 3700679913173 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2205605228251109 - 1) / 2 = 1102802614125554 from by norm_num]
      have h2 : (2 : ZMod 2205605228251109) ^ 1102802614125554 = ((2205605228251108 : ℕ) : ZMod 2205605228251109) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2205605228251109 - 1) / 149 = 14802719652692 from by norm_num]
      have h2 : (2 : ZMod 2205605228251109) ^ 14802719652692 = ((1225944915218980 : ℕ) : ZMod 2205605228251109) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3700679913173).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2205605228251109 - 1) / 3700679913173 = 596 from by norm_num]
      have h2 : (2 : ZMod 2205605228251109) ^ 596 = ((1169983832340898 : ℕ) : ZMod 2205605228251109) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3948098218524526031602723267 : Nat.Prime 3948098218524526031602723267 := by
  refine lucas_primality 3948098218524526031602723267 (3 : ZMod 3948098218524526031602723267) ?_ (fun q hq hd => ?_)
  · rw [show 3948098218524526031602723267 - 1 = 3948098218524526031602723266 from by norm_num]
    reduce_mod_char
  · have e : 3948098218524526031602723267 - 1 = [2 ^ 1, 3 ^ 1, 19 ^ 1, 877 ^ 1, 17904233 ^ 1, 2205605228251109 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3948098218524526031602723267 - 1) / 2 = 1974049109262263015801361633 from by norm_num]
      have h2 : (3 : ZMod 3948098218524526031602723267) ^ 1974049109262263015801361633 = ((3948098218524526031602723266 : ℕ) : ZMod 3948098218524526031602723267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3948098218524526031602723267 - 1) / 3 = 1316032739508175343867574422 from by norm_num]
      have h2 : (3 : ZMod 3948098218524526031602723267) ^ 1316032739508175343867574422 = ((1449384274203302192145547946 : ℕ) : ZMod 3948098218524526031602723267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3948098218524526031602723267 - 1) / 19 = 207794643080238212189617014 from by norm_num]
      have h2 : (3 : ZMod 3948098218524526031602723267) ^ 207794643080238212189617014 = ((3065202049728776225059749708 : ℕ) : ZMod 3948098218524526031602723267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3948098218524526031602723267 - 1) / 877 = 4501822370039368337061258 from by norm_num]
      have h2 : (3 : ZMod 3948098218524526031602723267) ^ 4501822370039368337061258 = ((764534461944947761420780630 : ℕ) : ZMod 3948098218524526031602723267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3948098218524526031602723267 - 1) / 17904233 = 220511999510089375602 from by norm_num]
      have h2 : (3 : ZMod 3948098218524526031602723267) ^ 220511999510089375602 = ((1387932479706490353659762186 : ℕ) : ZMod 3948098218524526031602723267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2205605228251109).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3948098218524526031602723267 - 1) / 2205605228251109 = 1790029406874 from by norm_num]
      have h2 : (3 : ZMod 3948098218524526031602723267) ^ 1790029406874 = ((3618927675776194795492501533 : ℕ) : ZMod 3948098218524526031602723267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18192836590961015953625348814337 : Nat.Prime 18192836590961015953625348814337 := by
  refine lucas_primality 18192836590961015953625348814337 (5 : ZMod 18192836590961015953625348814337) ?_ (fun q hq hd => ?_)
  · rw [show 18192836590961015953625348814337 - 1 = 18192836590961015953625348814336 from by norm_num]
    reduce_mod_char
  · have e : 18192836590961015953625348814337 - 1 = [2 ^ 9, 3 ^ 2, 3948098218524526031602723267 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18192836590961015953625348814337 - 1) / 2 = 9096418295480507976812674407168 from by norm_num]
      have h2 : (5 : ZMod 18192836590961015953625348814337) ^ 9096418295480507976812674407168 = ((18192836590961015953625348814336 : ℕ) : ZMod 18192836590961015953625348814337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18192836590961015953625348814337 - 1) / 3 = 6064278863653671984541782938112 from by norm_num]
      have h2 : (5 : ZMod 18192836590961015953625348814337) ^ 6064278863653671984541782938112 = ((11161093422296057261829870804451 : ℕ) : ZMod 18192836590961015953625348814337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3948098218524526031602723267).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18192836590961015953625348814337 - 1) / 3948098218524526031602723267 = 4608 from by norm_num]
      have h2 : (5 : ZMod 18192836590961015953625348814337) ^ 4608 = ((13685060387690013615354365845324 : ℕ) : ZMod 18192836590961015953625348814337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_146246987 : Nat.Prime 146246987 := by
  refine lucas_primality 146246987 (2 : ZMod 146246987) ?_ (fun q hq hd => ?_)
  · rw [show 146246987 - 1 = 146246986 from by norm_num]
    reduce_mod_char
  · have e : 146246987 - 1 = [2 ^ 1, 47 ^ 1, 1555819 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146246987 - 1) / 2 = 73123493 from by norm_num]
      have h2 : (2 : ZMod 146246987) ^ 73123493 = ((146246986 : ℕ) : ZMod 146246987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146246987 - 1) / 47 = 3111638 from by norm_num]
      have h2 : (2 : ZMod 146246987) ^ 3111638 = ((123299410 : ℕ) : ZMod 146246987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146246987 - 1) / 1555819 = 94 from by norm_num]
      have h2 : (2 : ZMod 146246987) ^ 94 = ((56970332 : ℕ) : ZMod 146246987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_81754966841140318493187568203841 : Nat.Prime 81754966841140318493187568203841 := by
  refine lucas_primality 81754966841140318493187568203841 (13 : ZMod 81754966841140318493187568203841) ?_ (fun q hq hd => ?_)
  · rw [show 81754966841140318493187568203841 - 1 = 81754966841140318493187568203840 from by norm_num]
    reduce_mod_char
  · have e : 81754966841140318493187568203841 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 1, 9601 ^ 1, 22153 ^ 1, 67187 ^ 1, 13583149 ^ 1, 146246987 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81754966841140318493187568203841 - 1) / 2 = 40877483420570159246593784101920 from by norm_num]
      have h2 : (13 : ZMod 81754966841140318493187568203841) ^ 40877483420570159246593784101920 = ((81754966841140318493187568203840 : ℕ) : ZMod 81754966841140318493187568203841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81754966841140318493187568203841 - 1) / 3 = 27251655613713439497729189401280 from by norm_num]
      have h2 : (13 : ZMod 81754966841140318493187568203841) ^ 27251655613713439497729189401280 = ((79766443076872509863360 : ℕ) : ZMod 81754966841140318493187568203841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81754966841140318493187568203841 - 1) / 5 = 16350993368228063698637513640768 from by norm_num]
      have h2 : (13 : ZMod 81754966841140318493187568203841) ^ 16350993368228063698637513640768 = ((1232001851013662848268580655749 : ℕ) : ZMod 81754966841140318493187568203841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81754966841140318493187568203841 - 1) / 9601 = 8515255373517375116465739840 from by norm_num]
      have h2 : (13 : ZMod 81754966841140318493187568203841) ^ 8515255373517375116465739840 = ((37491920500279748145372786684123 : ℕ) : ZMod 81754966841140318493187568203841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81754966841140318493187568203841 - 1) / 22153 = 3690469319782436622271817280 from by norm_num]
      have h2 : (13 : ZMod 81754966841140318493187568203841) ^ 3690469319782436622271817280 = ((77322044406592839324173636920936 : ℕ) : ZMod 81754966841140318493187568203841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81754966841140318493187568203841 - 1) / 67187 = 1216827166581932791956592320 from by norm_num]
      have h2 : (13 : ZMod 81754966841140318493187568203841) ^ 1216827166581932791956592320 = ((63502780328954593853900101133046 : ℕ) : ZMod 81754966841140318493187568203841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81754966841140318493187568203841 - 1) / 13583149 = 6018852244140170920100160 from by norm_num]
      have h2 : (13 : ZMod 81754966841140318493187568203841) ^ 6018852244140170920100160 = ((52894695054873076229047073130335 : ℕ) : ZMod 81754966841140318493187568203841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_146246987).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81754966841140318493187568203841 - 1) / 146246987 = 559019837045533926064320 from by norm_num]
      have h2 : (13 : ZMod 81754966841140318493187568203841) ^ 559019837045533926064320 = ((51393396244631358119088626626496 : ℕ) : ZMod 81754966841140318493187568203841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_77826286120321 : Nat.Prime 77826286120321 := by
  refine lucas_primality 77826286120321 (19 : ZMod 77826286120321) ?_ (fun q hq hd => ?_)
  · rw [show 77826286120321 - 1 = 77826286120320 from by norm_num]
    reduce_mod_char
  · have e : 77826286120321 - 1 = [2 ^ 7, 3 ^ 2, 5 ^ 1, 31 ^ 1, 101 ^ 1, 4315397 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77826286120321 - 1) / 2 = 38913143060160 from by norm_num]
      have h2 : (19 : ZMod 77826286120321) ^ 38913143060160 = ((77826286120320 : ℕ) : ZMod 77826286120321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77826286120321 - 1) / 3 = 25942095373440 from by norm_num]
      have h2 : (19 : ZMod 77826286120321) ^ 25942095373440 = ((57163819810927 : ℕ) : ZMod 77826286120321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77826286120321 - 1) / 5 = 15565257224064 from by norm_num]
      have h2 : (19 : ZMod 77826286120321) ^ 15565257224064 = ((69638365810545 : ℕ) : ZMod 77826286120321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77826286120321 - 1) / 31 = 2510525358720 from by norm_num]
      have h2 : (19 : ZMod 77826286120321) ^ 2510525358720 = ((23970497781618 : ℕ) : ZMod 77826286120321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77826286120321 - 1) / 101 = 770557288320 from by norm_num]
      have h2 : (19 : ZMod 77826286120321) ^ 770557288320 = ((52423691297286 : ℕ) : ZMod 77826286120321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77826286120321 - 1) / 4315397 = 18034560 from by norm_num]
      have h2 : (19 : ZMod 77826286120321) ^ 18034560 = ((69787835384391 : ℕ) : ZMod 77826286120321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_70613232600577 : Nat.Prime 70613232600577 := by
  refine lucas_primality 70613232600577 (5 : ZMod 70613232600577) ?_ (fun q hq hd => ?_)
  · rw [show 70613232600577 - 1 = 70613232600576 from by norm_num]
    reduce_mod_char
  · have e : 70613232600577 - 1 = [2 ^ 9, 3 ^ 1, 1889 ^ 1, 24336769 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70613232600577 - 1) / 2 = 35306616300288 from by norm_num]
      have h2 : (5 : ZMod 70613232600577) ^ 35306616300288 = ((70613232600576 : ℕ) : ZMod 70613232600577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70613232600577 - 1) / 3 = 23537744200192 from by norm_num]
      have h2 : (5 : ZMod 70613232600577) ^ 23537744200192 = ((53537091363738 : ℕ) : ZMod 70613232600577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70613232600577 - 1) / 1889 = 37381277184 from by norm_num]
      have h2 : (5 : ZMod 70613232600577) ^ 37381277184 = ((6390634014027 : ℕ) : ZMod 70613232600577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70613232600577 - 1) / 24336769 = 2901504 from by norm_num]
      have h2 : (5 : ZMod 70613232600577) ^ 2901504 = ((6975987075648 : ℕ) : ZMod 70613232600577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1207308227627 : Nat.Prime 1207308227627 := by
  refine lucas_primality 1207308227627 (2 : ZMod 1207308227627) ?_ (fun q hq hd => ?_)
  · rw [show 1207308227627 - 1 = 1207308227626 from by norm_num]
    reduce_mod_char
  · have e : 1207308227627 - 1 = [2 ^ 1, 29 ^ 1, 37 ^ 1, 151 ^ 1, 3725731 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1207308227627 - 1) / 2 = 603654113813 from by norm_num]
      have h2 : (2 : ZMod 1207308227627) ^ 603654113813 = ((1207308227626 : ℕ) : ZMod 1207308227627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1207308227627 - 1) / 29 = 41631318194 from by norm_num]
      have h2 : (2 : ZMod 1207308227627) ^ 41631318194 = ((256854226126 : ℕ) : ZMod 1207308227627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1207308227627 - 1) / 37 = 32629952098 from by norm_num]
      have h2 : (2 : ZMod 1207308227627) ^ 32629952098 = ((1190180623879 : ℕ) : ZMod 1207308227627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1207308227627 - 1) / 151 = 7995418726 from by norm_num]
      have h2 : (2 : ZMod 1207308227627) ^ 7995418726 = ((227640752954 : ℕ) : ZMod 1207308227627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1207308227627 - 1) / 3725731 = 324046 from by norm_num]
      have h2 : (2 : ZMod 1207308227627) ^ 324046 = ((6999750827 : ℕ) : ZMod 1207308227627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_267037263019450369 : Nat.Prime 267037263019450369 := by
  refine lucas_primality 267037263019450369 (14 : ZMod 267037263019450369) ?_ (fun q hq hd => ?_)
  · rw [show 267037263019450369 - 1 = 267037263019450368 from by norm_num]
    reduce_mod_char
  · have e : 267037263019450369 - 1 = [2 ^ 13, 3 ^ 3, 1207308227627 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267037263019450369 - 1) / 2 = 133518631509725184 from by norm_num]
      have h2 : (14 : ZMod 267037263019450369) ^ 133518631509725184 = ((267037263019450368 : ℕ) : ZMod 267037263019450369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267037263019450369 - 1) / 3 = 89012421006483456 from by norm_num]
      have h2 : (14 : ZMod 267037263019450369) ^ 89012421006483456 = ((14867999632763068 : ℕ) : ZMod 267037263019450369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1207308227627).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267037263019450369 - 1) / 1207308227627 = 221184 from by norm_num]
      have h2 : (14 : ZMod 267037263019450369) ^ 221184 = ((121162786380379227 : ℕ) : ZMod 267037263019450369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_762637039 : Nat.Prime 762637039 := by
  refine lucas_primality 762637039 (3 : ZMod 762637039) ?_ (fun q hq hd => ?_)
  · rw [show 762637039 - 1 = 762637038 from by norm_num]
    reduce_mod_char
  · have e : 762637039 - 1 = [2 ^ 1, 3 ^ 1, 197 ^ 1, 401 ^ 1, 1609 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (762637039 - 1) / 2 = 381318519 from by norm_num]
      have h2 : (3 : ZMod 762637039) ^ 381318519 = ((762637038 : ℕ) : ZMod 762637039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (762637039 - 1) / 3 = 254212346 from by norm_num]
      have h2 : (3 : ZMod 762637039) ^ 254212346 = ((576432349 : ℕ) : ZMod 762637039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (762637039 - 1) / 197 = 3871254 from by norm_num]
      have h2 : (3 : ZMod 762637039) ^ 3871254 = ((581049169 : ℕ) : ZMod 762637039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (762637039 - 1) / 401 = 1901838 from by norm_num]
      have h2 : (3 : ZMod 762637039) ^ 1901838 = ((20836505 : ℕ) : ZMod 762637039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (762637039 - 1) / 1609 = 473982 from by norm_num]
      have h2 : (3 : ZMod 762637039) ^ 473982 = ((251644563 : ℕ) : ZMod 762637039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56227703611393 : Nat.Prime 56227703611393 := by
  refine lucas_primality 56227703611393 (5 : ZMod 56227703611393) ?_ (fun q hq hd => ?_)
  · rw [show 56227703611393 - 1 = 56227703611392 from by norm_num]
    reduce_mod_char
  · have e : 56227703611393 - 1 = [2 ^ 13, 3 ^ 2, 762637039 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56227703611393 - 1) / 2 = 28113851805696 from by norm_num]
      have h2 : (5 : ZMod 56227703611393) ^ 28113851805696 = ((56227703611392 : ℕ) : ZMod 56227703611393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56227703611393 - 1) / 3 = 18742567870464 from by norm_num]
      have h2 : (5 : ZMod 56227703611393) ^ 18742567870464 = ((282429536480 : ℕ) : ZMod 56227703611393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_762637039).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56227703611393 - 1) / 762637039 = 73728 from by norm_num]
      have h2 : (5 : ZMod 56227703611393) ^ 73728 = ((43247451382596 : ℕ) : ZMod 56227703611393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_282429005041 : Nat.Prime 282429005041 := by
  refine lucas_primality 282429005041 (23 : ZMod 282429005041) ?_ (fun q hq hd => ?_)
  · rw [show 282429005041 - 1 = 282429005040 from by norm_num]
    reduce_mod_char
  · have e : 282429005041 - 1 = [2 ^ 4, 3 ^ 12, 5 ^ 1, 7 ^ 1, 13 ^ 1, 73 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (282429005041 - 1) / 2 = 141214502520 from by norm_num]
      have h2 : (23 : ZMod 282429005041) ^ 141214502520 = ((282429005040 : ℕ) : ZMod 282429005041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (282429005041 - 1) / 3 = 94143001680 from by norm_num]
      have h2 : (23 : ZMod 282429005041) ^ 94143001680 = ((282428473600 : ℕ) : ZMod 282429005041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (282429005041 - 1) / 5 = 56485801008 from by norm_num]
      have h2 : (23 : ZMod 282429005041) ^ 56485801008 = ((18056097776 : ℕ) : ZMod 282429005041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (282429005041 - 1) / 7 = 40347000720 from by norm_num]
      have h2 : (23 : ZMod 282429005041) ^ 40347000720 = ((117537977120 : ℕ) : ZMod 282429005041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (282429005041 - 1) / 13 = 21725308080 from by norm_num]
      have h2 : (23 : ZMod 282429005041) ^ 21725308080 = ((42380761108 : ℕ) : ZMod 282429005041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (282429005041 - 1) / 73 = 3868890480 from by norm_num]
      have h2 : (23 : ZMod 282429005041) ^ 3868890480 = ((163331267057 : ℕ) : ZMod 282429005041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_24127552321 : Nat.Prime 24127552321 := by
  refine lucas_primality 24127552321 (17 : ZMod 24127552321) ?_ (fun q hq hd => ?_)
  · rw [show 24127552321 - 1 = 24127552320 from by norm_num]
    reduce_mod_char
  · have e : 24127552321 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 25132867 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24127552321 - 1) / 2 = 12063776160 from by norm_num]
      have h2 : (17 : ZMod 24127552321) ^ 12063776160 = ((24127552320 : ℕ) : ZMod 24127552321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24127552321 - 1) / 3 = 8042517440 from by norm_num]
      have h2 : (17 : ZMod 24127552321) ^ 8042517440 = ((24084505600 : ℕ) : ZMod 24127552321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24127552321 - 1) / 5 = 4825510464 from by norm_num]
      have h2 : (17 : ZMod 24127552321) ^ 4825510464 = ((16106982316 : ℕ) : ZMod 24127552321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24127552321 - 1) / 25132867 = 960 from by norm_num]
      have h2 : (17 : ZMod 24127552321) ^ 960 = ((10607377509 : ℕ) : ZMod 24127552321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_602627329 : Nat.Prime 602627329 := by
  refine lucas_primality 602627329 (7 : ZMod 602627329) ?_ (fun q hq hd => ?_)
  · rw [show 602627329 - 1 = 602627328 from by norm_num]
    reduce_mod_char
  · have e : 602627329 - 1 = [2 ^ 8, 3 ^ 2, 261557 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (602627329 - 1) / 2 = 301313664 from by norm_num]
      have h2 : (7 : ZMod 602627329) ^ 301313664 = ((602627328 : ℕ) : ZMod 602627329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (602627329 - 1) / 3 = 200875776 from by norm_num]
      have h2 : (7 : ZMod 602627329) ^ 200875776 = ((18413135 : ℕ) : ZMod 602627329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (602627329 - 1) / 261557 = 2304 from by norm_num]
      have h2 : (7 : ZMod 602627329) ^ 2304 = ((83228881 : ℕ) : ZMod 602627329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_96948097 : Nat.Prime 96948097 := by
  refine lucas_primality 96948097 (15 : ZMod 96948097) ?_ (fun q hq hd => ?_)
  · rw [show 96948097 - 1 = 96948096 from by norm_num]
    reduce_mod_char
  · have e : 96948097 - 1 = [2 ^ 7, 3 ^ 1, 7 ^ 1, 36067 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96948097 - 1) / 2 = 48474048 from by norm_num]
      have h2 : (15 : ZMod 96948097) ^ 48474048 = ((96948096 : ℕ) : ZMod 96948097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96948097 - 1) / 3 = 32316032 from by norm_num]
      have h2 : (15 : ZMod 96948097) ^ 32316032 = ((74652472 : ℕ) : ZMod 96948097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96948097 - 1) / 7 = 13849728 from by norm_num]
      have h2 : (15 : ZMod 96948097) ^ 13849728 = ((95051727 : ℕ) : ZMod 96948097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96948097 - 1) / 36067 = 2688 from by norm_num]
      have h2 : (15 : ZMod 96948097) ^ 2688 = ((8431534 : ℕ) : ZMod 96948097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1418632417 : Nat.Prime 1418632417 := by
  refine lucas_primality 1418632417 (10 : ZMod 1418632417) ?_ (fun q hq hd => ?_)
  · rw [show 1418632417 - 1 = 1418632416 from by norm_num]
    reduce_mod_char
  · have e : 1418632417 - 1 = [2 ^ 5, 3 ^ 2, 19 ^ 1, 31 ^ 1, 8363 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1418632417 - 1) / 2 = 709316208 from by norm_num]
      have h2 : (10 : ZMod 1418632417) ^ 709316208 = ((1418632416 : ℕ) : ZMod 1418632417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1418632417 - 1) / 3 = 472877472 from by norm_num]
      have h2 : (10 : ZMod 1418632417) ^ 472877472 = ((1296946919 : ℕ) : ZMod 1418632417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1418632417 - 1) / 19 = 74664864 from by norm_num]
      have h2 : (10 : ZMod 1418632417) ^ 74664864 = ((737920624 : ℕ) : ZMod 1418632417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1418632417 - 1) / 31 = 45762336 from by norm_num]
      have h2 : (10 : ZMod 1418632417) ^ 45762336 = ((557946074 : ℕ) : ZMod 1418632417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1418632417 - 1) / 8363 = 169632 from by norm_num]
      have h2 : (10 : ZMod 1418632417) ^ 169632 = ((864750683 : ℕ) : ZMod 1418632417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 : Nat.Prime 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 := by
  refine lucas_primality 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ?_ (fun q hq hd => ?_)
  · rw [show 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1 = 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045440 from by norm_num]
    reduce_mod_char
  · have e : 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 19 ^ 1, 37 ^ 1, 41 ^ 1, 73 ^ 1, 97 ^ 1, 193 ^ 1, 577 ^ 1, 757 ^ 1, 769 ^ 1, 1153 ^ 1, 6481 ^ 1, 7297 ^ 1, 64513 ^ 1, 68737 ^ 1, 76801 ^ 1, 530713 ^ 1, 21523361 ^ 1, 96948097 ^ 1, 602627329 ^ 1, 1418632417 ^ 1, 24127552321 ^ 1, 282429005041 ^ 1, 56227703611393 ^ 1, 70613232600577 ^ 1, 77826286120321 ^ 1, 926510094425921 ^ 1, 267037263019450369 ^ 1, 185901652872784317405136897 ^ 1, 18192836590961015953625348814337 ^ 1, 81754966841140318493187568203841 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 2 = 24881352627368430912865084341059111877258627347179769931159473019198530598972722744608465517463494531262332637023719318023954533974086595940842691056110554096863924793648222591445044022465171220656751503051322823473185584180221391355431168002631157545836827246267310224522720 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 24881352627368430912865084341059111877258627347179769931159473019198530598972722744608465517463494531262332637023719318023954533974086595940842691056110554096863924793648222591445044022465171220656751503051322823473185584180221391355431168002631157545836827246267310224522720 = ((49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045440 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 3 = 16587568418245620608576722894039407918172418231453179954106315346132353732648481829738977011642329687508221758015812878682636355982724397293895127370740369397909283195765481727630029348310114147104501002034215215648790389453480927570287445335087438363891218164178206816348480 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 16587568418245620608576722894039407918172418231453179954106315346132353732648481829738977011642329687508221758015812878682636355982724397293895127370740369397909283195765481727630029348310114147104501002034215215648790389453480927570287445335087438363891218164178206816348480 = ((386378203013848318039046744743315765907590011756725873064404675434438622097746720502746888617049516470079889697815921361393398513002466241 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 5 = 9952541050947372365146033736423644750903450938871907972463789207679412239589089097843386206985397812504933054809487727209581813589634638376337076422444221638745569917459289036578017608986068488262700601220529129389274233672088556542172467201052463018334730898506924089809088 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 9952541050947372365146033736423644750903450938871907972463789207679412239589089097843386206985397812504933054809487727209581813589634638376337076422444221638745569917459289036578017608986068488262700601220529129389274233672088556542172467201052463018334730898506924089809088 = ((17688399657990156640800527499522962960706735953355881842308168683107326206458811683484477706357825911250814368815913300007112755859054752797738130887590927241241387029446173195995452023474435755626870823092648742264208340616892576438721290757659218821572118954221179857892357 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 7 = 7108957893533837403675738383159746250645322099194219980331278005485294456849349355602418719275284151789237896292491233721129866849739027411669340301745872599103978512470920740412869720704334634473357572300377949563767309765777540387266048000751759298810522070362088635577920 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 7108957893533837403675738383159746250645322099194219980331278005485294456849349355602418719275284151789237896292491233721129866849739027411669340301745872599103978512470920740412869720704334634473357572300377949563767309765777540387266048000751759298810522070362088635577920 = ((4793389893005151092882747975631681197372811888872599688581904680860533861800096839929696218962916822477362544895489784888296053917740170978935863415767962614098608296576598737728712156532950411132355809883258938350223731409715369871994516239644882732418616097537374865462061 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 13 = 3827900404210527832748474514009094134962865745719964604793765079876697015226572729939763925763614543271128098003649125849839159072936399375514260162478546784132911506715111167914622157302334033947192538930972742072797782181572521746989410461943255007051819576348816957618880 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 3827900404210527832748474514009094134962865745719964604793765079876697015226572729939763925763614543271128098003649125849839159072936399375514260162478546784132911506715111167914622157302334033947192538930972742072797782181572521746989410461943255007051819576348816957618880 = ((2728601724113309202551874292911137038763097053847475896692022716092328118694078450107633575823738882458199018485416937487197126591166005347022292945660387138916738218366279611379188009342359596525890754188701378729427621343646037121551364159383533940508942248609563165451730 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 17 = 2927217956160991872101774628359895514971603217315267050724643884611591835173261499365701825583940533089686192591025802120465239291069011287157963653660065187866344093370379128405299296760608378900794294476626214526257127550614281335933078588544842064216097323090271791120320 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 2927217956160991872101774628359895514971603217315267050724643884611591835173261499365701825583940533089686192591025802120465239291069011287157963653660065187866344093370379128405299296760608378900794294476626214526257127550614281335933078588544842064216097323090271791120320 = ((28702739800560009290657737441929319217080357966316000257943692115341195415535494034080644366814603812330315896173665503353612356036672238939458382715085381633503120462021141966379663074721667631211984027291154503808636651921146856524661009330027608848265896089916814245392619 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 19 = 2619089750249308517143693088532538092343013404966291571700997159915634799891865552064049001838262582238140277581444138739363635155167010099036072742748479378617255241436655009625794107627912760069131737163297139312966903597918041195308544000276963952193350236449190549949760 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 2619089750249308517143693088532538092343013404966291571700997159915634799891865552064049001838262582238140277581444138739363635155167010099036072742748479378617255241436655009625794107627912760069131737163297139312966903597918041195308544000276963952193350236449190549949760 = ((22159157828083077986595125788082676495173573338193304831410823584161477573652240079656795780094691094809957398895046006063612145539661119221022282373612807557166511453725498622557383250351699885611712803817266204625407134287808672203894813196268728949776078560651402065195111 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 37 = 1344937979857753022317031586003195236608574451198906482765376919956677329674201229438295433376405109797963926325606449622916461295896572753559064381411381302533185123980985004942975352565684930846310892056828260728280301847579534667861144216358440948423612283582016768893120 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 1344937979857753022317031586003195236608574451198906482765376919956677329674201229438295433376405109797963926325606449622916461295896572753559064381411381302533185123980985004942975352565684930846310892056828260728280301847579534667861144216358440948423612283582016768893120 = ((7518087522826050380564461282316808638060137613097800037520808905302168636698767303562334974496858180342588374211730149467903051206249589673214987410086374693037524967380991655127554003420201240746729295901894436770958843709559617352934067312967974974277903013427162613397343 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 41 = 1213724518408216142090979723954103018402859870594135118593145025326757590193791353395534903290902172256699153025547283806046562632882272972724033710054173370578728038714547443485124098656837620519841536734210869437716369960010799578313715512323471099796918402256941962171840 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 1213724518408216142090979723954103018402859870594135118593145025326757590193791353395534903290902172256699153025547283806046562632882272972724033710054173370578728038714547443485124098656837620519841536734210869437716369960010799578313715512323471099796918402256941962171840 = ((24514207667912892118888527906216110311433891981282829395852051849180698231018715364948803654800134361192361780534566228032629865536291103078420541591874542804360111536032937120871720553080196558980233790730393219486488358535510718713064807908608515247676309924899872910519631 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 73 = 681680893900504956516851625782441421294756913621363559757793781347904947917060897112560699108588891267461168137636145699286425588331139614817607974140015180735997939552006098395754630752470444401554835700036241738991385867951270996039210082263867330022926773870337266425280 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 681680893900504956516851625782441421294756913621363559757793781347904947917060897112560699108588891267461168137636145699286425588331139614817607974140015180735997939552006098395754630752470444401554835700036241738991385867951270996039210082263867330022926773870337266425280 = ((19171531353198746091990283138096251399757838914929547645096922258295473309258941519749940527166675669654588178917334122281044451759996560814164281451308536541180700927264622264767825862549212371235044101274898275757751295305011151772777406543613905419879888625305980595262230 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 97 = 513017579945740843564228543114620863448631491694428246003288103488629496886035520507391041597185454252831600763375656041731021319053331875068921465074444414368328346260788094668969979844642705580551577382501501514911042972788069924854250886652188815378078912294171344835520 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 513017579945740843564228543114620863448631491694428246003288103488629496886035520507391041597185454252831600763375656041731021319053331875068921465074444414368328346260788094668969979844642705580551577382501501514911042972788069924854250886652188815378078912294171344835520 = ((38813125636717856476505936896660352964636008379333296617525910511144261096265531663514888447355977133948286709708617772287095531907315465026092476286340582717570990544203740896874019988921258145229891961839373711103053210838964893496739183998769053150585545466904539454182998 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 193 = 257837851060812755573731443948799086810970231576992434519787285173041767865002308234284616761279736075257333026152531792994347502322140890578680736332751855926051034131069664160052269662851515239966336819184692471224721079587786438916385160649027539335096655401733784710080 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 257837851060812755573731443948799086810970231576992434519787285173041767865002308234284616761279736075257333026152531792994347502322140890578680736332751855926051034131069664160052269662851515239966336819184692471224721079587786438916385160649027539335096655401733784710080 = ((28359829989781694865573145081260443426320724017240145679817435273968137299479881775781848167213994065949739805628113286999932653455356608531507561588675037892801849651287460233938509862930357862913171853809554688863095533736183976997008218176312114776956433045168260615565462 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 577 = 86243856593998027427608611234173698014761273300449809120136821557013970880321395995176656906285942915987288169926236804242476720880716103781083851147696894616512737586302331339497552937487595218914216648358138036302203064749467561024024845763019610210872884735761907190720 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 86243856593998027427608611234173698014761273300449809120136821557013970880321395995176656906285942915987288169926236804242476720880716103781083851147696894616512737586302331339497552937487595218914216648358138036302203064749467561024024845763019610210872884735761907190720 = ((49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047431787155700879409885708048879996817194557126520500886510392092556765920247388685516985608791801240243349750196304233142772319501338591992887572576699903297883734 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 757 = 65736730851699949571638267743881405223932965250144702592231104410035747949729782680603607707961676436624392700194767022520355439825856264044498523265813881365558585980576545816235255013118021719040294591945370735728363498494640399882248792609329346224139570003348243657920 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 65736730851699949571638267743881405223932965250144702592231104410035747949729782680603607707961676436624392700194767022520355439825856264044498523265813881365558585980576545816235255013118021719040294591945370735728363498494640399882248792609329346224139570003348243657920 = ((43475364036212152901073312465047262955020898326546687396088131847168260762717896655596296500724213652253700079385670552969846872247085356966932632887172496834809313585997393085730075924930643428933945160136259296963115149685023205531534933995355065301264575862238158831395163 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 769 = 64710930110190977666749244059971682385588107534927880185070150895184734977822425863741132685210648975974857313455706938943964977825972941328589573617972832501596683468525936518712728276892512927585829656830488487576555485514229886490068057224008212082800591017600286669760 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 64710930110190977666749244059971682385588107534927880185070150895184734977822425863741132685210648975974857313455706938943964977825972941328589573617972832501596683468525936518712728276892512927585829656830488487576555485514229886490068057224008212082800591017600286669760 = ((13196620479688207436578495497220015519011706383947553645831670288607165595828508614769374868072057726059751445069942205058921502487064039623999225095343813535043024644896611144420365586638156282544725780950243948236854066793295703090245108267377008718167612996152877390580033 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 1153 = 43159328061350270447294161909903056161766916473859097885792667856372125930568469635053712953102332231157558780613563431090987916693992360695303887347980145874872376051427966333816208191613480001139204688727359624411423389731520193157729692979412242056958937114080329964480 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 43159328061350270447294161909903056161766916473859097885792667856372125930568469635053712953102332231157558780613563431090987916693992360695303887347980145874872376051427966333816208191613480001139204688727359624411423389731520193157729692979412242056958937114080329964480 = ((33878802990496233633236667429362049689789877294491624995870689643146683663094585596862885001308699897697743421695164359907768621677896949154530614841050395107934736906469490324585517408536572976225250887443575635514599041398965930663984484951155271060191512370767743464909311 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 6481 = 7678244908924064469330376281764885627915021554445230653034862835734772596504466207254579699880726595050866420930016762235443460569074709440161299508134718128950447398132455667781220189003293078431338220352205777958088438259596170762361107237349531722214728358669128290240 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 7678244908924064469330376281764885627915021554445230653034862835734772596504466207254579699880726595050866420930016762235443460569074709440161299508134718128950447398132455667781220189003293078431338220352205777958088438259596170762361107237349531722214728358669128290240 = ((48323181191908701991703738604540305381486849448278297054471596208074103054741023896956311843919972090882308527091398560332859054939538850533114804308262971653505638998499599809659876637324165119370192349100766424601042468444246810932188482629762851429298117652698760886093421 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 7297 = 6819611519081384380667420677280830992807627065144516905895429085706051966280039124190342748379743601826047043174926495278595185411562723294735560108568056488108517142290865449210646573239734471880704811032293496909191608655672575402338267233830658502353522611009266883520 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 6819611519081384380667420677280830992807627065144516905895429085706051966280039124190342748379743601826047043174926495278595185411562723294735560108568056488108517142290865449210646573239734471880704811032293496909191608655672575402338267233830658502353522611009266883520 = ((376094358169676876758717247772526144566342598907798866005289209133933261600001738999468196332809141547464524184697839402815316229020105123618823177161609868655447693852905893200238333963247334513512122112933796863064183774172549860756450820479272322616707364823422680331657 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 64513 = 771359342376526619839879848745496624781319341750647774282996388920017069396020112058297258458403563041939845830258066374961776199342352578266169331952026850305021462144008884765707501510243554652759955452430450404513372008129257401002314820350352876035429362958390098880 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 771359342376526619839879848745496624781319341750647774282996388920017069396020112058297258458403563041939845830258066374961776199342352578266169331952026850305021462144008884765707501510243554652759955452430450404513372008129257401002314820350352876035429362958390098880 = ((37345471176329004069777467523646571356535866075535152034331766531276802420664391882896094998181697077769547205825077125189810073438734165139849011371887174091553300049372051004936723987082181326249548835743080098299279382883582368803707048083082782437295115345800454204906122 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 68737 = 723958061229568672268649616394637877046092420302886943892211560562681833625928473590888910411088483095344069046473349666815675225106903005392807106976171613450221126719182466253838370090785784094643394476084869094466898007775183419568243246072163683193529750971596381120 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 723958061229568672268649616394637877046092420302886943892211560562681833625928473590888910411088483095344069046473349666815675225106903005392807106976171613450221126719182466253838370090785784094643394476084869094466898007775183419568243246072163683193529750971596381120 = ((45950932401876347205480601559124470582605865032941758298766460939831317712287737581120021514248393603276604131757016129169788315974933777447654324476654186574521275686818428850111513869574674671122142145634814119296880693761414595570963189870335704974876692195872350499951182 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 76801 = 647943454573988122885511499617429769853481786622043200769767920188500946575506119571580201233408276748019755915254210701005313315558042107286173124206990901078473582209820772944233643376132373814318863115098054022035795996932888669559801773482927502137649958887704853440 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 647943454573988122885511499617429769853481786622043200769767920188500946575506119571580201233408276748019755915254210701005313315558042107286173124206990901078473582209820772944233643376132373814318863115098054022035795996932888669559801773482927502137649958887704853440 = ((18181868334792221554692623026050309455784778186056537830947649649449071828924198131756865572880688898717127597221961358083492175527745667637080334710259592358041717596466677333263099084310717713594184852732395802282259671048847905797200861186834124875028417370442632448440328 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 530713 = 93765755228790065111896955006035698681805900165173153592090161798179168774734075647698343614961361531608732542913851057064569867231767814019414225979429763721122055776467592056139736627763673475708156774193670867203876988806459956154950672030386131660000140363123986880 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 93765755228790065111896955006035698681805900165173153592090161798179168774734075647698343614961361531608732542913851057064569867231767814019414225979429763721122055776467592056139736627763673475708156774193670867203876988806459956154950672030386131660000140363123986880 = ((8203238820115182122534329186100452312247248289245819396537837376519134671355669956869862751024820480367978476421411431085395754924521513443768579455353981324628674889859059482619723950054323940067490225512178599204611415110735409713024612726980203819670725961797217223396664 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 21523361 = 2312032272967816774793219733763617297248197188829362656804341386942172330703622240467784331402841269192328524994188344285444502275837551202234882466182726210545269839004068425135372121711397325042009145602429176695329840370211826243627207479596811812600906266104751040 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 2312032272967816774793219733763617297248197188829362656804341386942172330703622240467784331402841269192328524994188344285444502275837551202234882466182726210545269839004068425135372121711397325042009145602429176695329840370211826243627207479596811812600906266104751040 = ((35861629354629724570834260193828514285471486986079591431580965823256074281943374798893086615210148338677102230787333938243728760793289034925366665135341545637635199538752356186423344866190018062741248949816365040088054360284385566998869211623225515221092834966620099904217700 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_96948097).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 96948097 = 513292233624109835036062323968238631383525296988135206638650638376089643079280302832730497380747855860694875465657037456319633256423518987501996889244985470872397315723447827788616501105022643624593301775718667762466458401555244376904709496311849371232873756073155520 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 513292233624109835036062323968238631383525296988135206638650638376089643079280302832730497380747855860694875465657037456319633256423518987501996889244985470872397315723447827788616501105022643624593301775718667762466458401555244376904709496311849371232873756073155520 = ((19415486747375341941060098106365522331093904627280245328474962863324445929664604833311587385454624145212082044852185293004889205607501540699353032338191110429842052342801433929155449908031543340794605202546383781695371172746999416332499421258424406219099433189462389531392485 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_602627329).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 602627329 = 82576250461978072397925001310583151058051757713031862619557610601488438633265909334850180740686237717115987738497400001001131277848458133702869924294822527362890058355279876765910973222607271502141754022746362448733836245187019692415679236487567783524257749838183360 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 82576250461978072397925001310583151058051757713031862619557610601488438633265909334850180740686237717115987738497400001001131277848458133702869924294822527362890058355279876765910973222607271502141754022746362448733836245187019692415679236487567783524257749838183360 = ((26800004334949595989798933482140020795203383124017658997303427078551454565755885604993794466604743801876354625012782182598699758611825556268536438131619459035864653882223309207256752219948198850650783380136160671828019697856000021946179486795014976969727418906445119451384037 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1418632417).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 1418632417 = 35077941726420355602046113882168691309777996349254113979773060577394842654258510074084209394551703002938403369396174341085784639833288958235955341285720181166371760407401183179708833655484091790152221656233762524366712796159403414162121417253122247728583841104016320 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 35077941726420355602046113882168691309777996349254113979773060577394842654258510074084209394551703002938403369396174341085784639833288958235955341285720181166371760407401183179708833655484091790152221656233762524366712796159403414162121417253122247728583841104016320 = ((12191947524133747842109179255524656151069605327050681260705919509652690912120656800925858340211977245176061091498715551712713419554278470227969597690838610973195483535429326181075158785650890769992240888002233882416241468312729065916350410807415226633752455030686915751627888 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_24127552321).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 24127552321 = 2062484606506259032711690733550817682817750367292200715659944129912350639471459442668632521786543018083407569457258193465629209522839156456913497044498694144753973760838682181833992428084654963178164938818148657863037741844896972991662560946157332968349618380360640 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 2062484606506259032711690733550817682817750367292200715659944129912350639471459442668632521786543018083407569457258193465629209522839156456913497044498694144753973760838682181833992428084654963178164938818148657863037741844896972991662560946157332968349618380360640 = ((5594613208678141798978607573112193343816750335622393428110644999727405529285615203043100419645707916479068905254102218676972066427944079549988974223934226507652035065887337828623197107740102784042862636257409626045907117896497331241641257554885478016419430266066744427025953 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_282429005041).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 282429005041 = 176195448649167065652886179273088082452156935205083151848764742886792759616127041714273370487007100678478027234595963397702281210962661792588251509847944959796045403465761541173130800984240197287667585407200916369234574888021239930020613494971655484881362590971840 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 176195448649167065652886179273088082452156935205083151848764742886792759616127041714273370487007100678478027234595963397702281210962661792588251509847944959796045403465761541173130800984240197287667585407200916369234574888021239930020613494971655484881362590971840 = ((35641416857701045148278470060134061641955209473482766622240907977155137074578330979372655003174184598454063472901884165713038736776477937483225032160567749762067654939471473221983100854696281001418415564158978450078337636369257562815340632347907947752360627950360075754593145 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_56227703611393).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 56227703611393 = 885021120525608949101416013102227975699216913550393716705857260440691898179257007630321504842583259221938315149898730908603438442868476273715094989683786961135301722318283556231129515465203595325533416316842849595738791347619445245980737444127164627629090438080 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 885021120525608949101416013102227975699216913550393716705857260440691898179257007630321504842583259221938315149898730908603438442868476273715094989683786961135301722318283556231129515465203595325533416316842849595738791347619445245980737444127164627629090438080 = ((25258779588656124622497422190889444860748143595029599045812916125379876811203138905716986373824196896840032433680440902726070276713827963462407306101103696420327870650241616246928429380116011475327593587604666555640202998428072776622572140636243796594646780007867474717422177 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_70613232600577).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 70613232600577 = 704722095591049844906464923992265912683534576814447387464555898207526792148015930517639633495808985156099247743720620575296849812767627204475531420653849609542030488526178782969503691679977540232510980744825535873521343847405464444222447097273181105102771190720 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 704722095591049844906464923992265912683534576814447387464555898207526792148015930517639633495808985156099247743720620575296849812767627204475531420653849609542030488526178782969503691679977540232510980744825535873521343847405464444222447097273181105102771190720 = ((1261589511798772789262077855145220515338754920620734553333273834934065619298361611262259702984267769814751659917263535622025865358183782086173429099160665343598665071401979845408465184835720815178848706068237332503221408505645963243036196242596557285966206863450840793990772 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_77826286120321).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 77826286120321 = 639407425632551975642212740575485570463098487966765710645240464999847008100821535123980901610472366622390533317686356981374762115619656312113014296769488845865344032528192156632856404926073781089892682166352744058847195283813098815574810719047874320574855240640 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 639407425632551975642212740575485570463098487966765710645240464999847008100821535123980901610472366622390533317686356981374762115619656312113014296769488845865344032528192156632856404926073781089892682166352744058847195283813098815574810719047874320574855240640 = ((16446275249479910579020002296555564554416538939321247276527419422122028602702263298485373415672322421069857197111194682283947780354570190926928515337409902582862860329249066666560793827808599492052800984990231661586624401429478935981823481132875998385120408624226198370394426 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_926510094425921).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 926510094425921 = 53709836033217264390242291538123098635456772908560622425697930037037862146205869837013109484888708031292513755010746688098118904905027715527113374856763786603020172636728435074428963803166599660710206695290784064659553648377824400950488715698794330472267336640 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 53709836033217264390242291538123098635456772908560622425697930037037862146205869837013109484888708031292513755010746688098118904905027715527113374856763786603020172636728435074428963803166599660710206695290784064659553648377824400950488715698794330472267336640 = ((33835428687420708343115205915834545490308793728587451787770322295696678922162637635735085795317055928970743027827274340825122341132953275078501572584162291417125169510476553326057693921180174637439897483654845278314734193952191063534747651315240464655687510281352348216033597 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_267037263019450369).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 267037263019450369 = 186351165721438145839848746258522544606823736831581659309419269741379019548163542217502944023394512333221814727000191657739246215740397051641744288141828078824066471650464999818248229936660493091739821298821338169161196337967533368015178847820778813556685760 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 186351165721438145839848746258522544606823736831581659309419269741379019548163542217502944023394512333221814727000191657739246215740397051641744288141828078824066471650464999818248229936660493091739821298821338169161196337967533368015178847820778813556685760 = ((27229007275027453042427254975461899107198335291762998415562320728531345523436476171898632444527418671919685205510662249568171282437117484541869234373822555332663608174783021447516287106512404921800780826915006501462568435324562756202669424036275514694489258030742357567161619 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_185901652872784317405136897).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 185901652872784317405136897 = 267682962930890844063655981727798692233221995614135881368245214184333962420419134244521412606208789806169621076508838568263750098790126595702139442695855419518954723740641630470545511844903381011840804473171110680357346834277120780726891760382147520 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 267682962930890844063655981727798692233221995614135881368245214184333962420419134244521412606208789806169621076508838568263750098790126595702139442695855419518954723740641630470545511844903381011840804473171110680357346834277120780726891760382147520 = ((20467133510502644755833011899241302373572073188185296149365729162254963221115953650050737021826076770883932549700719680378502359010311422462678137493908169562392040960976826635386079398277960241407132615604077389650906934095455827460791940752526168665855310298134044986591770 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_18192836590961015953625348814337).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 18192836590961015953625348814337 = 2735291168363547829520865235522215825995919645526382922799199479572218495665744991974187487262021437134011252934879509459406465697564233424612036895848887680247834661732401852530222801699780229234756268247921862772469502072222269367643781725120 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 2735291168363547829520865235522215825995919645526382922799199479572218495665744991974187487262021437134011252934879509459406465697564233424612036895848887680247834661732401852530222801699780229234756268247921862772469502072222269367643781725120 = ((39820307716844802519962367016616009752838614122349745954068842991517314365735340525261775848902762658609023282898304212104014068029026426644336909368595346878570957635888146358134733029352705999797745192146394881663236330932006548190362195084048789336484728355102629365378273 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_81754966841140318493187568203841).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 - 1) / 81754966841140318493187568203841 = 608681125777125585603775949803771582288758576120727712594822832823730445476095980040214619229916812494554172714177078075861713966680062029656383376479233090191314988731606354304369182691072222969151228850726368033904299415661398065765243259840 from by norm_num]
      have h2 : (11 : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) ^ 608681125777125585603775949803771582288758576120727712594822832823730445476095980040214619229916812494554172714177078075861713966680062029656383376479233090191314988731606354304369182691072222969151228850726368033904299415661398065765243259840 = ((11851449901322115482615048022201824475815852032392176626178649360862041354772461559387075049466994696621048460259475965191627081240648499299743970957944898494594575784641985856659692949742218713177703932136975240161339653266538080837689893927268148798449431693425185591141047 : ℕ) : ZMod 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_53703966166793 : Nat.Prime 53703966166793 := by
  refine lucas_primality 53703966166793 (3 : ZMod 53703966166793) ?_ (fun q hq hd => ?_)
  · rw [show 53703966166793 - 1 = 53703966166792 from by norm_num]
    reduce_mod_char
  · have e : 53703966166793 - 1 = [2 ^ 3, 571 ^ 1, 2777 ^ 1, 4233547 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53703966166793 - 1) / 2 = 26851983083396 from by norm_num]
      have h2 : (3 : ZMod 53703966166793) ^ 26851983083396 = ((53703966166792 : ℕ) : ZMod 53703966166793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53703966166793 - 1) / 571 = 94052480152 from by norm_num]
      have h2 : (3 : ZMod 53703966166793) ^ 94052480152 = ((27715010421277 : ℕ) : ZMod 53703966166793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53703966166793 - 1) / 2777 = 19338842696 from by norm_num]
      have h2 : (3 : ZMod 53703966166793) ^ 19338842696 = ((39632805164518 : ℕ) : ZMod 53703966166793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53703966166793 - 1) / 4233547 = 12685336 from by norm_num]
      have h2 : (3 : ZMod 53703966166793) ^ 12685336 = ((48885674061648 : ℕ) : ZMod 53703966166793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_119137231 : Nat.Prime 119137231 := by
  refine lucas_primality 119137231 (6 : ZMod 119137231) ?_ (fun q hq hd => ?_)
  · rw [show 119137231 - 1 = 119137230 from by norm_num]
    reduce_mod_char
  · have e : 119137231 - 1 = [2 ^ 1, 3 ^ 4, 5 ^ 1, 147083 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119137231 - 1) / 2 = 59568615 from by norm_num]
      have h2 : (6 : ZMod 119137231) ^ 59568615 = ((119137230 : ℕ) : ZMod 119137231) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119137231 - 1) / 3 = 39712410 from by norm_num]
      have h2 : (6 : ZMod 119137231) ^ 39712410 = ((47470962 : ℕ) : ZMod 119137231) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119137231 - 1) / 5 = 23827446 from by norm_num]
      have h2 : (6 : ZMod 119137231) ^ 23827446 = ((104918197 : ℕ) : ZMod 119137231) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119137231 - 1) / 147083 = 810 from by norm_num]
      have h2 : (6 : ZMod 119137231) ^ 810 = ((38164409 : ℕ) : ZMod 119137231) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- 3^577 + 1: 11 divides 1297 + 1 and 5741 + 1 (chains 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 -> 53703966166793 -> 119137231 -> 1297; 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 -> 53703966166793 -> 119137231 -> 5741).
theorem kill3_e577 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 577 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 : 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 ∈ P := S7 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 prime_49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 577 = 3 ^ 200 * (3 ^ 200 * 3 ^ 177) by rw [← pow_add, ← pow_add]]; norm_num : 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 ∣ 1 + 3 ^ 577).trans hd)
  have g53703966166793 : 53703966166793 ∈ P := S1 53703966166793 prime_53703966166793 (by norm_num) (hnz (by norm_num)) 49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 g49762705254736861825730168682118223754517254694359539862318946038397061197945445489216931034926989062524665274047438636047909067948173191881685382112221108193727849587296445182890088044930342441313503006102645646946371168360442782710862336005262315091673654492534620449045441 (by norm_num)
  have g119137231 : 119137231 ∈ P := S1 119137231 prime_119137231 (by norm_num) (hnz (by norm_num)) 53703966166793 g53703966166793 (by norm_num)
  have g1297 : 1297 ∈ P := S1 1297 (by norm_num) (by norm_num) (hnz (by norm_num)) 119137231 g119137231 (by norm_num)
  have g5741 : 5741 ∈ P := S1 5741 (by norm_num) (by norm_num) (hnz (by norm_num)) 119137231 g119137231 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1297 g1297 5741 g5741 (by norm_num) (by norm_num)
  omega

-- The balance equation of n, in the form used by the kill lemmas.
theorem kill_at {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hiff : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3)
    (k : ∀ (m : ℕ) (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
      (2 ^ m + 1) * (1 + 3 ^ n.factorization 3) * ∏ p ∈ P, (p + 1) =
        2 ^ (m + 1) * 3 ^ n.factorization 3 * ∏ p ∈ P, p → False) : False := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he' =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
    omega
  have h3sq := (hiff 3).mpr rfl
  have he2 : 2 ≤ n.factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn0).mp h3sq.2.2
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  exact k _ _ hP E

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hiff he hG => ?_⟩
  rcases he with he | he
  · exact (kill_at h hiff (fun _ _ hP E => kill3_e577 hP E (by rw [he]))).elim
  · rcases Nat.mod_two_eq_zero_or_one (padicValNat 2 n) with hp | hp
    · exact (h2 n h hiff he hp hG).trans (le_max_right _ _)
    · exact (h1 n h hiff he hp hG).trans (le_max_left _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1
