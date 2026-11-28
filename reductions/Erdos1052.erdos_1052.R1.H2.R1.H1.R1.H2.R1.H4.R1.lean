import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- Splits step H4 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1 (the unitary perfect number n has
-- exactly one repeated odd prime z, 7 <= z < 2100, exponent e = v_z(n), a = padicValNat 2 n) by
-- e mod 8, after sieving the prime z in the classes e odd, e = 2 mod 4 and e = 4 mod 8.
-- Proving H1, ..., H4 proves the step.
--
-- Notation as in the parent file: P = the set of simple odd primes of n.  The balance equation is
--   (2^a + 1)(1 + z^e) prod_P (p + 1) = 2^(a+1) z^e prod_P p,
-- in which every odd prime other than z occurs exactly once on the left.  If e is odd then z + 1
-- divides 1 + z^e; if e = 2 mod 4 then z^2 + 1 does; if e = 4 mod 8 then z^4 + 1 does.  Their odd
-- primes are simple primes of n, and the odd primes (other than z) of p + 1 for simple p are
-- simple again.
--
-- PROVED BELOW (no hypothesis needed):
--  * zsieve (there are 314 primes z in [7, 2100)):
--    - e odd: z is one of 69 primes.  For the other 245 the forced chain from z + 1 ends in a
--      contradiction: an odd square divides z + 1 (80), a square divides some p + 1 (54), a prime
--      has two sources on the left (110), or the forced primes are too abundant (1, see below).
--    - e = 2 mod 4: z is one of 5 primes, 11, 139, 181, 199, 271 (309 excluded from z^2 + 1: 38, 159, 107
--      and 5 cases).
--    - e = 4 mod 8: z is one of 9 primes (305 excluded from z^4 + 1: 8, 234, 63 and 0 cases);
--      z = 7 is then excluded by the parent's condition on e, leaving 8.
--    Primes above 4.3 * 10^7 on the chains carry a Lucas certificate (theorems prime_<p>, 73 new,
--    up to 13 digits).
--  * weight_kill: distinct simple primes p_1, ..., p_k with prod (p_i + 1) >= 2 prod p_i are
--    impossible, because the balance equation gives prod_P (p + 1)/p < 2.
--  * odd_divisor_mod_six: if z = 2 mod 3, d is odd and e is an odd multiple of d, then d = 1 mod 6.
--    So for z = 2 mod 3 and e odd every divisor of e is 1 mod 6.
--  * not_odd_odd: if z = 2 mod 3 then a and e are not both odd (3 would divide 2^a + 1 and 1 + z^e).
--  * odd_two_divisor: if a is odd and d divides a then d = 1 mod 6, unless z = 2 mod 3 and z divides
--    2^d + 1 (this exception is real: z = 11, d = 5).
--
-- H1 (OPEN): e odd, z in the list of 69.          H2 (OPEN): e = 2 mod 4, z in the list of 5.
-- H3 (OPEN): e = 4 mod 8, z in the list of 8.     H4 (OPEN): 8 divides e.
-- Each H keeps the conditions of the parent step; those left out are vacuous there or follow from
-- the listed ones (z = 1 mod 3 -> a mod 6 != 5 follows from the divisor clause for odd a).
-- No known unitary perfect number has a repeated odd prime z >= 7.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main

-- H1: a is bounded when e is odd.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    Odd (n.factorization z) →
    z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ) →
    (z % 3 = 2 → ∀ d, d ∣ n.factorization z → d % 6 = 1) →
    (z % 3 = 2 → Even (padicValNat 2 n)) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when e = 2 mod 4.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 4 = 2 →
    z ∈ ({11, 139, 181, 199, 271} : Finset ℕ) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H3: a is bounded when e = 4 mod 8.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 8 = 4 →
    z ∈ ({11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H4: a is bounded when 8 divides e.
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 7 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 8 = 0 →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- Section 1. Uniform lemmas.

theorem odd_of_dvd_odd {d m : ℕ} (hd : d ∣ m) (hm : m % 2 = 1) : d % 2 = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rcases Nat.even_or_odd d with ⟨j, rfl⟩ | h
  · exfalso
    have : (j + j) * k = 2 * (j * k) := by ring
    omega
  · exact Nat.odd_iff.mp h

-- 2^d + 1 divides 2^m + 1 when m is an odd multiple of d.
theorem tpd {d m : ℕ} (h : m % (2 * d) = d) : 2 ^ d + 1 ∣ 2 ^ m + 1 := by
  have := one_add_pow_dvd_of_odd_mul (z := 2) h
  rwa [add_comm 1 (2 ^ d), add_comm 1 (2 ^ m)] at this

-- If z = 2 mod 3, d is odd and 1 + z^d divides 1 + z^e then d = 1 mod 6.
theorem odd_divisor_mod_six {m e d z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 2) (hz2 : z ≠ 2)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (ho : d % 2 = 1) (hd : 1 + z ^ d ∣ 1 + z ^ e) : d % 6 = 1 := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := prime_dvd_prime_pow hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hzodd : z % 2 = 1 := by
    rcases hz.eq_two_or_odd with h | h
    · exact absurd h hz2
    · exact h
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := z) (Nat.odd_iff.mpr ho)
  have h6 : 6 ∣ z + 1 := by omega
  have hQ6 : Q % 6 = d % 6 := Nat.ModEq.of_dvd h6 hQm
  have h3z : 3 ∣ z + 1 := by omega
  have h3d : 3 ∣ 1 + z ^ d := by rw [hQ]; exact Dvd.dvd.mul_right h3z _
  have h3K : 3 ∣ 1 + z ^ e := h3d.trans hd
  by_contra hne
  have hcase : d % 6 = 3 ∨ d % 6 = 5 := by omega
  rcases hcase with h3 | h5
  · have h3Q : 3 ∣ Q := by omega
    have h9d : 3 * 3 ∣ 1 + z ^ d := by rw [hQ]; exact mul_dvd_mul h3z h3Q
    exact S_sq hP hK E (c := 3) Nat.prime_three (by norm_num) (hnz (by omega))
      (((h9d.trans hd).mul_left _).mul_right _)
  · have hQ3 : Q % 3 = 2 := by omega
    obtain ⟨r, hrp, hrd, hr3⟩ := exists_prime_mod3 Q hQ3
    have hrd' : r ∣ 1 + z ^ d := by rw [hQ]; exact hrd.mul_left _
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    have hrz : r ≠ z := by
      rintro rfl
      have h1 : r ∣ r ^ d := dvd_pow_self r (by omega)
      have h11 : r ∣ 1 := (Nat.dvd_add_left h1).mp hrd'
      exact hrp.one_lt.ne' (Nat.dvd_one.mp h11)
    have hrP : r ∈ P := S7 r hrp hr2 (hnz hrz) (hrd'.trans hd)
    exact S8 3 Nat.prime_three (by norm_num) (hnz (by omega)) h3K r hrP (by omega)

-- If z = 2 mod 3 then a and e are not both odd: 3 would divide both 2^a + 1 and 1 + z^e.
theorem not_odd_odd {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 2)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hm : m % 2 = 1) (he : e % 2 = 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h3 : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one hm
  obtain ⟨Q, hQ, -⟩ := exists_quot_mod (z := z) (Nat.odd_iff.mpr he)
  have h3z : 3 ∣ z + 1 := by omega
  have h3K : 3 ∣ 1 + z ^ e := by rw [hQ]; exact Dvd.dvd.mul_right h3z _
  exact S_sq hP (prime_dvd_prime_pow hz) E (c := 3) Nat.prime_three (by norm_num) (hnz (by omega))
    ((mul_dvd_mul h3 h3K).mul_right _)

-- If a is odd and d divides a then d = 1 mod 6, unless z = 2 mod 3 and z divides 2^d + 1.
theorem odd_two_divisor {m e d z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime) (hz7 : 7 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hm : m % 2 = 1) (hd : d ∣ m) : d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1) := by
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have ho : d % 2 = 1 := odd_of_dvd_odd hd hm
  have hdm : 2 ^ d + 1 ∣ 2 ^ m + 1 := tpd (mod_of_dvd_odd hd hm)
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := 2) (Nat.odd_iff.mpr ho)
  have hQ3' : Q % 3 = d % 3 := hQm
  have h3 : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one hm
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne1, hne2⟩ := hne
  have hcase : d % 6 = 3 ∨ d % 6 = 5 := by omega
  rcases hcase with h3' | h5
  · obtain ⟨t, ht⟩ : 3 ∣ Q := Nat.dvd_of_mod_eq_zero (by omega)
    exact S5 3 Nat.prime_three (by norm_num) (hnz (by omega))
      (Dvd.dvd.trans ⟨t, by rw [add_comm, hQ, ht]; ring⟩ hdm)
  · have hQ3 : Q % 3 = 2 := by omega
    obtain ⟨r, hrp, hrd, hr3⟩ := exists_prime_mod3 Q hQ3
    have hrd' : r ∣ 2 ^ d + 1 := by rw [add_comm, hQ]; exact hrd.mul_left _
    have hr2 : r ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
      have h11 : 2 ∣ 1 := (Nat.dvd_add_right h1).mp hrd'
      omega
    have hrz : r ≠ z := by
      rintro rfl
      exact hne2 ⟨hr3, hrd'⟩
    have hrP : r ∈ P := S2 r hrp hr2 (hnz hrz) (hrd'.trans hdm)
    exact S4 3 Nat.prime_three (by norm_num) (hnz (by omega)) h3 r hrP (by omega)

-- Weight bound: a list L of distinct simple primes whose weight prod (p + 1)/p is at least 2 is
-- impossible, since the balance equation gives prod over P of (p + 1)/p = 2 (2^m/(2^m+1)) (z^e/(z^e+1)) < 2.
theorem weight_kill {m e z : ℕ} {P : Finset ℕ} {L : List ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hL : L.Nodup) (hsub : ∀ x ∈ L, x ∈ P) (hw : 2 * L.prod ≤ (L.map (fun p => p + 1)).prod) :
    False := by
  have hF : L.toFinset ⊆ P := fun x hx => hsub x (List.mem_toFinset.mp hx)
  have hA : ∏ p ∈ L.toFinset, p = L.prod := by
    rw [List.prod_toFinset _ hL, List.map_id']
  have hB : ∏ p ∈ L.toFinset, (p + 1) = (L.map (fun p => p + 1)).prod := List.prod_toFinset _ hL
  have h1 := Finset.prod_sdiff hF (f := fun p => p + 1)
  have h2 := Finset.prod_sdiff hF (f := fun p => p)
  have hQ : ∏ p ∈ P \ L.toFinset, p ≤ ∏ p ∈ P \ L.toFinset, (p + 1) :=
    Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => Nat.le_succ i)
  have hpos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hP p hp).1.pos)
  rw [← h1] at E
  rw [← h2] at hpos E
  rw [hA] at hpos E
  rw [hB] at E
  have h3 : 2 ^ (m + 1) * z ^ e < 2 * ((2 ^ m + 1) * (1 + z ^ e)) := by
    rw [pow_succ]
    nlinarith [Nat.zero_le (2 ^ m), Nat.zero_le (z ^ e)]
  have key : 2 ^ (m + 1) * z ^ e * ((∏ p ∈ P \ L.toFinset, p) * L.prod) <
      (2 ^ m + 1) * (1 + z ^ e) * ((∏ p ∈ P \ L.toFinset, (p + 1)) * (L.map (fun p => p + 1)).prod) :=
    calc 2 ^ (m + 1) * z ^ e * ((∏ p ∈ P \ L.toFinset, p) * L.prod)
        < 2 * ((2 ^ m + 1) * (1 + z ^ e)) * ((∏ p ∈ P \ L.toFinset, p) * L.prod) :=
          Nat.mul_lt_mul_of_pos_right h3 hpos
      _ = (2 ^ m + 1) * (1 + z ^ e) * ((∏ p ∈ P \ L.toFinset, p) * (2 * L.prod)) := by ring
      _ ≤ (2 ^ m + 1) * (1 + z ^ e) * ((∏ p ∈ P \ L.toFinset, (p + 1)) * (L.map (fun p => p + 1)).prod) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hw)
  omega

-- Section 2. Lucas certificates and the sieve of z, in ranges of 300.

theorem prime_56275441 : Nat.Prime 56275441 := by
  refine lucas_primality 56275441 (7 : ZMod 56275441) ?_ (fun q hq hd => ?_)
  · rw [show 56275441 - 1 = 56275440 from by norm_num]
    reduce_mod_char
  · have e : 56275441 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 1061 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56275441 - 1) / 2 = 28137720 from by norm_num]
      have h2 : (7 : ZMod 56275441) ^ 28137720 = ((56275440 : ℕ) : ZMod 56275441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56275441 - 1) / 3 = 18758480 from by norm_num]
      have h2 : (7 : ZMod 56275441) ^ 18758480 = ((37218072 : ℕ) : ZMod 56275441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56275441 - 1) / 5 = 11255088 from by norm_num]
      have h2 : (7 : ZMod 56275441) ^ 11255088 = ((35636403 : ℕ) : ZMod 56275441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56275441 - 1) / 13 = 4328880 from by norm_num]
      have h2 : (7 : ZMod 56275441) ^ 4328880 = ((40489030 : ℕ) : ZMod 56275441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56275441 - 1) / 17 = 3310320 from by norm_num]
      have h2 : (7 : ZMod 56275441) ^ 3310320 = ((29450191 : ℕ) : ZMod 56275441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56275441 - 1) / 1061 = 53040 from by norm_num]
      have h2 : (7 : ZMod 56275441) ^ 53040 = ((20060778 : ℕ) : ZMod 56275441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_81523681 : Nat.Prime 81523681 := by
  refine lucas_primality 81523681 (22 : ZMod 81523681) ?_ (fun q hq hd => ?_)
  · rw [show 81523681 - 1 = 81523680 from by norm_num]
    reduce_mod_char
  · have e : 81523681 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 19 ^ 1, 1277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81523681 - 1) / 2 = 40761840 from by norm_num]
      have h2 : (22 : ZMod 81523681) ^ 40761840 = ((81523680 : ℕ) : ZMod 81523681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81523681 - 1) / 3 = 27174560 from by norm_num]
      have h2 : (22 : ZMod 81523681) ^ 27174560 = ((11881048 : ℕ) : ZMod 81523681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81523681 - 1) / 5 = 16304736 from by norm_num]
      have h2 : (22 : ZMod 81523681) ^ 16304736 = ((49028037 : ℕ) : ZMod 81523681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81523681 - 1) / 7 = 11646240 from by norm_num]
      have h2 : (22 : ZMod 81523681) ^ 11646240 = ((75186877 : ℕ) : ZMod 81523681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81523681 - 1) / 19 = 4290720 from by norm_num]
      have h2 : (22 : ZMod 81523681) ^ 4290720 = ((72545144 : ℕ) : ZMod 81523681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81523681 - 1) / 1277 = 63840 from by norm_num]
      have h2 : (22 : ZMod 81523681) ^ 63840 = ((52849799 : ℕ) : ZMod 81523681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_784119601 : Nat.Prime 784119601 := by
  refine lucas_primality 784119601 (13 : ZMod 784119601) ?_ (fun q hq hd => ?_)
  · rw [show 784119601 - 1 = 784119600 from by norm_num]
    reduce_mod_char
  · have e : 784119601 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 2, 11 ^ 1, 19801 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784119601 - 1) / 2 = 392059800 from by norm_num]
      have h2 : (13 : ZMod 784119601) ^ 392059800 = ((784119600 : ℕ) : ZMod 784119601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784119601 - 1) / 3 = 261373200 from by norm_num]
      have h2 : (13 : ZMod 784119601) ^ 261373200 = ((378648509 : ℕ) : ZMod 784119601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784119601 - 1) / 5 = 156823920 from by norm_num]
      have h2 : (13 : ZMod 784119601) ^ 156823920 = ((652172943 : ℕ) : ZMod 784119601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784119601 - 1) / 11 = 71283600 from by norm_num]
      have h2 : (13 : ZMod 784119601) ^ 71283600 = ((322817200 : ℕ) : ZMod 784119601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784119601 - 1) / 19801 = 39600 from by norm_num]
      have h2 : (13 : ZMod 784119601) ^ 39600 = ((669501567 : ℕ) : ZMod 784119601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56008543 : Nat.Prime 56008543 := by
  refine lucas_primality 56008543 (3 : ZMod 56008543) ?_ (fun q hq hd => ?_)
  · rw [show 56008543 - 1 = 56008542 from by norm_num]
    reduce_mod_char
  · have e : 56008543 - 1 = [2 ^ 1, 3 ^ 1, 19 ^ 1, 23 ^ 1, 41 ^ 1, 521 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56008543 - 1) / 2 = 28004271 from by norm_num]
      have h2 : (3 : ZMod 56008543) ^ 28004271 = ((56008542 : ℕ) : ZMod 56008543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56008543 - 1) / 3 = 18669514 from by norm_num]
      have h2 : (3 : ZMod 56008543) ^ 18669514 = ((19800 : ℕ) : ZMod 56008543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56008543 - 1) / 19 = 2947818 from by norm_num]
      have h2 : (3 : ZMod 56008543) ^ 2947818 = ((52552800 : ℕ) : ZMod 56008543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56008543 - 1) / 23 = 2435154 from by norm_num]
      have h2 : (3 : ZMod 56008543) ^ 2435154 = ((16608988 : ℕ) : ZMod 56008543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56008543 - 1) / 41 = 1366062 from by norm_num]
      have h2 : (3 : ZMod 56008543) ^ 1366062 = ((7036163 : ℕ) : ZMod 56008543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56008543 - 1) / 521 = 107502 from by norm_num]
      have h2 : (3 : ZMod 56008543) ^ 107502 = ((51798350 : ℕ) : ZMod 56008543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1984563001 : Nat.Prime 1984563001 := by
  refine lucas_primality 1984563001 (29 : ZMod 1984563001) ?_ (fun q hq hd => ?_)
  · rw [show 1984563001 - 1 = 1984563000 from by norm_num]
    reduce_mod_char
  · have e : 1984563001 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 3, 7 ^ 1, 17 ^ 2, 109 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1984563001 - 1) / 2 = 992281500 from by norm_num]
      have h2 : (29 : ZMod 1984563001) ^ 992281500 = ((1984563000 : ℕ) : ZMod 1984563001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1984563001 - 1) / 3 = 661521000 from by norm_num]
      have h2 : (29 : ZMod 1984563001) ^ 661521000 = ((838492286 : ℕ) : ZMod 1984563001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1984563001 - 1) / 5 = 396912600 from by norm_num]
      have h2 : (29 : ZMod 1984563001) ^ 396912600 = ((241507515 : ℕ) : ZMod 1984563001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1984563001 - 1) / 7 = 283509000 from by norm_num]
      have h2 : (29 : ZMod 1984563001) ^ 283509000 = ((1448017813 : ℕ) : ZMod 1984563001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1984563001 - 1) / 17 = 116739000 from by norm_num]
      have h2 : (29 : ZMod 1984563001) ^ 116739000 = ((810902460 : ℕ) : ZMod 1984563001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1984563001 - 1) / 109 = 18207000 from by norm_num]
      have h2 : (29 : ZMod 1984563001) ^ 18207000 = ((1273133478 : ℕ) : ZMod 1984563001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4798962481 : Nat.Prime 4798962481 := by
  refine lucas_primality 4798962481 (14 : ZMod 4798962481) ?_ (fun q hq hd => ?_)
  · rw [show 4798962481 - 1 = 4798962480 from by norm_num]
    reduce_mod_char
  · have e : 4798962481 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 13 ^ 1, 97 ^ 1, 101 ^ 1, 157 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4798962481 - 1) / 2 = 2399481240 from by norm_num]
      have h2 : (14 : ZMod 4798962481) ^ 2399481240 = ((4798962480 : ℕ) : ZMod 4798962481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4798962481 - 1) / 3 = 1599654160 from by norm_num]
      have h2 : (14 : ZMod 4798962481) ^ 1599654160 = ((465676610 : ℕ) : ZMod 4798962481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4798962481 - 1) / 5 = 959792496 from by norm_num]
      have h2 : (14 : ZMod 4798962481) ^ 959792496 = ((2668487277 : ℕ) : ZMod 4798962481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4798962481 - 1) / 13 = 369150960 from by norm_num]
      have h2 : (14 : ZMod 4798962481) ^ 369150960 = ((4062901204 : ℕ) : ZMod 4798962481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4798962481 - 1) / 97 = 49473840 from by norm_num]
      have h2 : (14 : ZMod 4798962481) ^ 49473840 = ((853673618 : ℕ) : ZMod 4798962481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4798962481 - 1) / 101 = 47514480 from by norm_num]
      have h2 : (14 : ZMod 4798962481) ^ 47514480 = ((10800947 : ℕ) : ZMod 4798962481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4798962481 - 1) / 157 = 30566640 from by norm_num]
      have h2 : (14 : ZMod 4798962481) ^ 30566640 = ((4409282821 : ℕ) : ZMod 4798962481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5049019561 : Nat.Prime 5049019561 := by
  refine lucas_primality 5049019561 (7 : ZMod 5049019561) ?_ (fun q hq hd => ?_)
  · rw [show 5049019561 - 1 = 5049019560 from by norm_num]
    reduce_mod_char
  · have e : 5049019561 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 13 ^ 1, 53 ^ 1, 79 ^ 1, 773 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5049019561 - 1) / 2 = 2524509780 from by norm_num]
      have h2 : (7 : ZMod 5049019561) ^ 2524509780 = ((5049019560 : ℕ) : ZMod 5049019561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5049019561 - 1) / 3 = 1683006520 from by norm_num]
      have h2 : (7 : ZMod 5049019561) ^ 1683006520 = ((2796029410 : ℕ) : ZMod 5049019561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5049019561 - 1) / 5 = 1009803912 from by norm_num]
      have h2 : (7 : ZMod 5049019561) ^ 1009803912 = ((2330268886 : ℕ) : ZMod 5049019561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5049019561 - 1) / 13 = 388386120 from by norm_num]
      have h2 : (7 : ZMod 5049019561) ^ 388386120 = ((4939876166 : ℕ) : ZMod 5049019561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5049019561 - 1) / 53 = 95264520 from by norm_num]
      have h2 : (7 : ZMod 5049019561) ^ 95264520 = ((11657607 : ℕ) : ZMod 5049019561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5049019561 - 1) / 79 = 63911640 from by norm_num]
      have h2 : (7 : ZMod 5049019561) ^ 63911640 = ((4150692034 : ℕ) : ZMod 5049019561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5049019561 - 1) / 773 = 6531720 from by norm_num]
      have h2 : (7 : ZMod 5049019561) ^ 6531720 = ((3126058535 : ℕ) : ZMod 5049019561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6448958881 : Nat.Prime 6448958881 := by
  refine lucas_primality 6448958881 (33 : ZMod 6448958881) ?_ (fun q hq hd => ?_)
  · rw [show 6448958881 - 1 = 6448958880 from by norm_num]
    reduce_mod_char
  · have e : 6448958881 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 2, 41 ^ 1, 277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6448958881 - 1) / 2 = 3224479440 from by norm_num]
      have h2 : (33 : ZMod 6448958881) ^ 3224479440 = ((6448958880 : ℕ) : ZMod 6448958881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6448958881 - 1) / 3 = 2149652960 from by norm_num]
      have h2 : (33 : ZMod 6448958881) ^ 2149652960 = ((3362900479 : ℕ) : ZMod 6448958881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6448958881 - 1) / 5 = 1289791776 from by norm_num]
      have h2 : (33 : ZMod 6448958881) ^ 1289791776 = ((5481888679 : ℕ) : ZMod 6448958881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6448958881 - 1) / 7 = 921279840 from by norm_num]
      have h2 : (33 : ZMod 6448958881) ^ 921279840 = ((4419023232 : ℕ) : ZMod 6448958881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6448958881 - 1) / 13 = 496073760 from by norm_num]
      have h2 : (33 : ZMod 6448958881) ^ 496073760 = ((2231418262 : ℕ) : ZMod 6448958881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6448958881 - 1) / 41 = 157291680 from by norm_num]
      have h2 : (33 : ZMod 6448958881) ^ 157291680 = ((5615337551 : ℕ) : ZMod 6448958881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6448958881 - 1) / 277 = 23281440 from by norm_num]
      have h2 : (33 : ZMod 6448958881) ^ 23281440 = ((4422668202 : ℕ) : ZMod 6448958881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7763701441 : Nat.Prime 7763701441 := by
  refine lucas_primality 7763701441 (14 : ZMod 7763701441) ?_ (fun q hq hd => ?_)
  · rw [show 7763701441 - 1 = 7763701440 from by norm_num]
    reduce_mod_char
  · have e : 7763701441 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 11 ^ 1, 17 ^ 1, 59 ^ 1, 733 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7763701441 - 1) / 2 = 3881850720 from by norm_num]
      have h2 : (14 : ZMod 7763701441) ^ 3881850720 = ((7763701440 : ℕ) : ZMod 7763701441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7763701441 - 1) / 3 = 2587900480 from by norm_num]
      have h2 : (14 : ZMod 7763701441) ^ 2587900480 = ((1840475653 : ℕ) : ZMod 7763701441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7763701441 - 1) / 5 = 1552740288 from by norm_num]
      have h2 : (14 : ZMod 7763701441) ^ 1552740288 = ((3740058504 : ℕ) : ZMod 7763701441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7763701441 - 1) / 11 = 705791040 from by norm_num]
      have h2 : (14 : ZMod 7763701441) ^ 705791040 = ((6725483554 : ℕ) : ZMod 7763701441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7763701441 - 1) / 17 = 456688320 from by norm_num]
      have h2 : (14 : ZMod 7763701441) ^ 456688320 = ((4368887298 : ℕ) : ZMod 7763701441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7763701441 - 1) / 59 = 131588160 from by norm_num]
      have h2 : (14 : ZMod 7763701441) ^ 131588160 = ((7241815458 : ℕ) : ZMod 7763701441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7763701441 - 1) / 733 = 10591680 from by norm_num]
      have h2 : (14 : ZMod 7763701441) ^ 10591680 = ((4458417147 : ℕ) : ZMod 7763701441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17253574561 : Nat.Prime 17253574561 := by
  refine lucas_primality 17253574561 (7 : ZMod 17253574561) ?_ (fun q hq hd => ?_)
  · rw [show 17253574561 - 1 = 17253574560 from by norm_num]
    reduce_mod_char
  · have e : 17253574561 - 1 = [2 ^ 5, 3 ^ 3, 5 ^ 1, 43 ^ 1, 293 ^ 1, 317 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17253574561 - 1) / 2 = 8626787280 from by norm_num]
      have h2 : (7 : ZMod 17253574561) ^ 8626787280 = ((17253574560 : ℕ) : ZMod 17253574561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17253574561 - 1) / 3 = 5751191520 from by norm_num]
      have h2 : (7 : ZMod 17253574561) ^ 5751191520 = ((10229116279 : ℕ) : ZMod 17253574561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17253574561 - 1) / 5 = 3450714912 from by norm_num]
      have h2 : (7 : ZMod 17253574561) ^ 3450714912 = ((11090913916 : ℕ) : ZMod 17253574561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17253574561 - 1) / 43 = 401245920 from by norm_num]
      have h2 : (7 : ZMod 17253574561) ^ 401245920 = ((11966555127 : ℕ) : ZMod 17253574561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17253574561 - 1) / 293 = 58885920 from by norm_num]
      have h2 : (7 : ZMod 17253574561) ^ 58885920 = ((13812547010 : ℕ) : ZMod 17253574561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17253574561 - 1) / 317 = 54427680 from by norm_num]
      have h2 : (7 : ZMod 17253574561) ^ 54427680 = ((7399972248 : ℕ) : ZMod 17253574561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_20321481601 : Nat.Prime 20321481601 := by
  refine lucas_primality 20321481601 (13 : ZMod 20321481601) ?_ (fun q hq hd => ?_)
  · rw [show 20321481601 - 1 = 20321481600 from by norm_num]
    reduce_mod_char
  · have e : 20321481601 - 1 = [2 ^ 7, 3 ^ 2, 5 ^ 2, 7 ^ 1, 100801 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20321481601 - 1) / 2 = 10160740800 from by norm_num]
      have h2 : (13 : ZMod 20321481601) ^ 10160740800 = ((20321481600 : ℕ) : ZMod 20321481601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20321481601 - 1) / 3 = 6773827200 from by norm_num]
      have h2 : (13 : ZMod 20321481601) ^ 6773827200 = ((14043162580 : ℕ) : ZMod 20321481601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20321481601 - 1) / 5 = 4064296320 from by norm_num]
      have h2 : (13 : ZMod 20321481601) ^ 4064296320 = ((8504590762 : ℕ) : ZMod 20321481601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20321481601 - 1) / 7 = 2903068800 from by norm_num]
      have h2 : (13 : ZMod 20321481601) ^ 2903068800 = ((14322227598 : ℕ) : ZMod 20321481601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20321481601 - 1) / 100801 = 201600 from by norm_num]
      have h2 : (13 : ZMod 20321481601) ^ 201600 = ((1048476484 : ℕ) : ZMod 20321481601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_26321586241 : Nat.Prime 26321586241 := by
  refine lucas_primality 26321586241 (13 : ZMod 26321586241) ?_ (fun q hq hd => ?_)
  · rw [show 26321586241 - 1 = 26321586240 from by norm_num]
    reduce_mod_char
  · have e : 26321586241 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 89 ^ 1, 239 ^ 1, 1289 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26321586241 - 1) / 2 = 13160793120 from by norm_num]
      have h2 : (13 : ZMod 26321586241) ^ 13160793120 = ((26321586240 : ℕ) : ZMod 26321586241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26321586241 - 1) / 3 = 8773862080 from by norm_num]
      have h2 : (13 : ZMod 26321586241) ^ 8773862080 = ((8867949972 : ℕ) : ZMod 26321586241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26321586241 - 1) / 5 = 5264317248 from by norm_num]
      have h2 : (13 : ZMod 26321586241) ^ 5264317248 = ((11517833039 : ℕ) : ZMod 26321586241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26321586241 - 1) / 89 = 295748160 from by norm_num]
      have h2 : (13 : ZMod 26321586241) ^ 295748160 = ((21758791253 : ℕ) : ZMod 26321586241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26321586241 - 1) / 239 = 110132160 from by norm_num]
      have h2 : (13 : ZMod 26321586241) ^ 110132160 = ((331025674 : ℕ) : ZMod 26321586241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26321586241 - 1) / 1289 = 20420160 from by norm_num]
      have h2 : (13 : ZMod 26321586241) ^ 20420160 = ((794323768 : ℕ) : ZMod 26321586241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_28124567281 : Nat.Prime 28124567281 := by
  refine lucas_primality 28124567281 (11 : ZMod 28124567281) ?_ (fun q hq hd => ?_)
  · rw [show 28124567281 - 1 = 28124567280 from by norm_num]
    reduce_mod_char
  · have e : 28124567281 - 1 = [2 ^ 4, 3 ^ 5, 5 ^ 1, 37 ^ 1, 61 ^ 1, 641 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28124567281 - 1) / 2 = 14062283640 from by norm_num]
      have h2 : (11 : ZMod 28124567281) ^ 14062283640 = ((28124567280 : ℕ) : ZMod 28124567281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28124567281 - 1) / 3 = 9374855760 from by norm_num]
      have h2 : (11 : ZMod 28124567281) ^ 9374855760 = ((10243947132 : ℕ) : ZMod 28124567281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28124567281 - 1) / 5 = 5624913456 from by norm_num]
      have h2 : (11 : ZMod 28124567281) ^ 5624913456 = ((17649935793 : ℕ) : ZMod 28124567281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28124567281 - 1) / 37 = 760123440 from by norm_num]
      have h2 : (11 : ZMod 28124567281) ^ 760123440 = ((16361808088 : ℕ) : ZMod 28124567281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28124567281 - 1) / 61 = 461058480 from by norm_num]
      have h2 : (11 : ZMod 28124567281) ^ 461058480 = ((25281495806 : ℕ) : ZMod 28124567281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28124567281 - 1) / 641 = 43876080 from by norm_num]
      have h2 : (11 : ZMod 28124567281) ^ 43876080 = ((16663159404 : ℕ) : ZMod 28124567281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_37409056921 : Nat.Prime 37409056921 := by
  refine lucas_primality 37409056921 (7 : ZMod 37409056921) ?_ (fun q hq hd => ?_)
  · rw [show 37409056921 - 1 = 37409056920 from by norm_num]
    reduce_mod_char
  · have e : 37409056921 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 17 ^ 1, 29 ^ 1, 131 ^ 1, 1609 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37409056921 - 1) / 2 = 18704528460 from by norm_num]
      have h2 : (7 : ZMod 37409056921) ^ 18704528460 = ((37409056920 : ℕ) : ZMod 37409056921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37409056921 - 1) / 3 = 12469685640 from by norm_num]
      have h2 : (7 : ZMod 37409056921) ^ 12469685640 = ((28674544094 : ℕ) : ZMod 37409056921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37409056921 - 1) / 5 = 7481811384 from by norm_num]
      have h2 : (7 : ZMod 37409056921) ^ 7481811384 = ((35011486946 : ℕ) : ZMod 37409056921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37409056921 - 1) / 17 = 2200532760 from by norm_num]
      have h2 : (7 : ZMod 37409056921) ^ 2200532760 = ((27162139824 : ℕ) : ZMod 37409056921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37409056921 - 1) / 29 = 1289967480 from by norm_num]
      have h2 : (7 : ZMod 37409056921) ^ 1289967480 = ((13845819277 : ℕ) : ZMod 37409056921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37409056921 - 1) / 131 = 285565320 from by norm_num]
      have h2 : (7 : ZMod 37409056921) ^ 285565320 = ((19162817955 : ℕ) : ZMod 37409056921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37409056921 - 1) / 1609 = 23249880 from by norm_num]
      have h2 : (7 : ZMod 37409056921) ^ 23249880 = ((4285122425 : ℕ) : ZMod 37409056921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1351728281 : Nat.Prime 1351728281 := by
  refine lucas_primality 1351728281 (3 : ZMod 1351728281) ?_ (fun q hq hd => ?_)
  · rw [show 1351728281 - 1 = 1351728280 from by norm_num]
    reduce_mod_char
  · have e : 1351728281 - 1 = [2 ^ 3, 5 ^ 1, 7 ^ 1, 29 ^ 1, 61 ^ 1, 2729 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1351728281 - 1) / 2 = 675864140 from by norm_num]
      have h2 : (3 : ZMod 1351728281) ^ 675864140 = ((1351728280 : ℕ) : ZMod 1351728281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1351728281 - 1) / 5 = 270345656 from by norm_num]
      have h2 : (3 : ZMod 1351728281) ^ 270345656 = ((597493821 : ℕ) : ZMod 1351728281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1351728281 - 1) / 7 = 193104040 from by norm_num]
      have h2 : (3 : ZMod 1351728281) ^ 193104040 = ((1312225023 : ℕ) : ZMod 1351728281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1351728281 - 1) / 29 = 46611320 from by norm_num]
      have h2 : (3 : ZMod 1351728281) ^ 46611320 = ((334438398 : ℕ) : ZMod 1351728281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1351728281 - 1) / 61 = 22159480 from by norm_num]
      have h2 : (3 : ZMod 1351728281) ^ 22159480 = ((31785685 : ℕ) : ZMod 1351728281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1351728281 - 1) / 2729 = 495320 from by norm_num]
      have h2 : (3 : ZMod 1351728281) ^ 495320 = ((900488063 : ℕ) : ZMod 1351728281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1591050761 : Nat.Prime 1591050761 := by
  refine lucas_primality 1591050761 (3 : ZMod 1591050761) ?_ (fun q hq hd => ?_)
  · rw [show 1591050761 - 1 = 1591050760 from by norm_num]
    reduce_mod_char
  · have e : 1591050761 - 1 = [2 ^ 3, 5 ^ 1, 13 ^ 1, 23 ^ 1, 151 ^ 1, 881 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591050761 - 1) / 2 = 795525380 from by norm_num]
      have h2 : (3 : ZMod 1591050761) ^ 795525380 = ((1591050760 : ℕ) : ZMod 1591050761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591050761 - 1) / 5 = 318210152 from by norm_num]
      have h2 : (3 : ZMod 1591050761) ^ 318210152 = ((400475302 : ℕ) : ZMod 1591050761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591050761 - 1) / 13 = 122388520 from by norm_num]
      have h2 : (3 : ZMod 1591050761) ^ 122388520 = ((386931056 : ℕ) : ZMod 1591050761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591050761 - 1) / 23 = 69176120 from by norm_num]
      have h2 : (3 : ZMod 1591050761) ^ 69176120 = ((738065055 : ℕ) : ZMod 1591050761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591050761 - 1) / 151 = 10536760 from by norm_num]
      have h2 : (3 : ZMod 1591050761) ^ 10536760 = ((901629735 : ℕ) : ZMod 1591050761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591050761 - 1) / 881 = 1805960 from by norm_num]
      have h2 : (3 : ZMod 1591050761) ^ 1805960 = ((1379619861 : ℕ) : ZMod 1591050761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_70601170681 : Nat.Prime 70601170681 := by
  refine lucas_primality 70601170681 (7 : ZMod 70601170681) ?_ (fun q hq hd => ?_)
  · rw [show 70601170681 - 1 = 70601170680 from by norm_num]
    reduce_mod_char
  · have e : 70601170681 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 17 ^ 1, 53 ^ 1, 307 ^ 1, 709 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70601170681 - 1) / 2 = 35300585340 from by norm_num]
      have h2 : (7 : ZMod 70601170681) ^ 35300585340 = ((70601170680 : ℕ) : ZMod 70601170681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70601170681 - 1) / 3 = 23533723560 from by norm_num]
      have h2 : (7 : ZMod 70601170681) ^ 23533723560 = ((2760327190 : ℕ) : ZMod 70601170681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70601170681 - 1) / 5 = 14120234136 from by norm_num]
      have h2 : (7 : ZMod 70601170681) ^ 14120234136 = ((51698544790 : ℕ) : ZMod 70601170681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70601170681 - 1) / 17 = 4153010040 from by norm_num]
      have h2 : (7 : ZMod 70601170681) ^ 4153010040 = ((59695626717 : ℕ) : ZMod 70601170681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70601170681 - 1) / 53 = 1332097560 from by norm_num]
      have h2 : (7 : ZMod 70601170681) ^ 1332097560 = ((38831522941 : ℕ) : ZMod 70601170681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70601170681 - 1) / 307 = 229971240 from by norm_num]
      have h2 : (7 : ZMod 70601170681) ^ 229971240 = ((48617660000 : ℕ) : ZMod 70601170681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70601170681 - 1) / 709 = 99578520 from by norm_num]
      have h2 : (7 : ZMod 70601170681) ^ 99578520 = ((70189957901 : ℕ) : ZMod 70601170681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_85470037801 : Nat.Prime 85470037801 := by
  refine lucas_primality 85470037801 (26 : ZMod 85470037801) ?_ (fun q hq hd => ?_)
  · rw [show 85470037801 - 1 = 85470037800 from by norm_num]
    reduce_mod_char
  · have e : 85470037801 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 2, 7 ^ 1, 23 ^ 1, 107 ^ 1, 8269 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85470037801 - 1) / 2 = 42735018900 from by norm_num]
      have h2 : (26 : ZMod 85470037801) ^ 42735018900 = ((85470037800 : ℕ) : ZMod 85470037801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85470037801 - 1) / 3 = 28490012600 from by norm_num]
      have h2 : (26 : ZMod 85470037801) ^ 28490012600 = ((70272853373 : ℕ) : ZMod 85470037801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85470037801 - 1) / 5 = 17094007560 from by norm_num]
      have h2 : (26 : ZMod 85470037801) ^ 17094007560 = ((74635233994 : ℕ) : ZMod 85470037801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85470037801 - 1) / 7 = 12210005400 from by norm_num]
      have h2 : (26 : ZMod 85470037801) ^ 12210005400 = ((33629036541 : ℕ) : ZMod 85470037801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85470037801 - 1) / 23 = 3716088600 from by norm_num]
      have h2 : (26 : ZMod 85470037801) ^ 3716088600 = ((74300920919 : ℕ) : ZMod 85470037801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85470037801 - 1) / 107 = 798785400 from by norm_num]
      have h2 : (26 : ZMod 85470037801) ^ 798785400 = ((11253728643 : ℕ) : ZMod 85470037801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85470037801 - 1) / 8269 = 10336200 from by norm_num]
      have h2 : (26 : ZMod 85470037801) ^ 10336200 = ((10977727657 : ℕ) : ZMod 85470037801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1200229417 : Nat.Prime 1200229417 := by
  refine lucas_primality 1200229417 (5 : ZMod 1200229417) ?_ (fun q hq hd => ?_)
  · rw [show 1200229417 - 1 = 1200229416 from by norm_num]
    reduce_mod_char
  · have e : 1200229417 - 1 = [2 ^ 3, 3 ^ 2, 43 ^ 1, 139 ^ 1, 2789 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1200229417 - 1) / 2 = 600114708 from by norm_num]
      have h2 : (5 : ZMod 1200229417) ^ 600114708 = ((1200229416 : ℕ) : ZMod 1200229417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1200229417 - 1) / 3 = 400076472 from by norm_num]
      have h2 : (5 : ZMod 1200229417) ^ 400076472 = ((341593494 : ℕ) : ZMod 1200229417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1200229417 - 1) / 43 = 27912312 from by norm_num]
      have h2 : (5 : ZMod 1200229417) ^ 27912312 = ((120931124 : ℕ) : ZMod 1200229417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1200229417 - 1) / 139 = 8634744 from by norm_num]
      have h2 : (5 : ZMod 1200229417) ^ 8634744 = ((729876564 : ℕ) : ZMod 1200229417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1200229417 - 1) / 2789 = 430344 from by norm_num]
      have h2 : (5 : ZMod 1200229417) ^ 430344 = ((291926584 : ℕ) : ZMod 1200229417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2299999841 : Nat.Prime 2299999841 := by
  refine lucas_primality 2299999841 (6 : ZMod 2299999841) ?_ (fun q hq hd => ?_)
  · rw [show 2299999841 - 1 = 2299999840 from by norm_num]
    reduce_mod_char
  · have e : 2299999841 - 1 = [2 ^ 5, 5 ^ 1, 137 ^ 1, 317 ^ 1, 331 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2299999841 - 1) / 2 = 1149999920 from by norm_num]
      have h2 : (6 : ZMod 2299999841) ^ 1149999920 = ((2299999840 : ℕ) : ZMod 2299999841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2299999841 - 1) / 5 = 459999968 from by norm_num]
      have h2 : (6 : ZMod 2299999841) ^ 459999968 = ((115175671 : ℕ) : ZMod 2299999841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2299999841 - 1) / 137 = 16788320 from by norm_num]
      have h2 : (6 : ZMod 2299999841) ^ 16788320 = ((471854269 : ℕ) : ZMod 2299999841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2299999841 - 1) / 317 = 7255520 from by norm_num]
      have h2 : (6 : ZMod 2299999841) ^ 7255520 = ((1268186854 : ℕ) : ZMod 2299999841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2299999841 - 1) / 331 = 6948640 from by norm_num]
      have h2 : (6 : ZMod 2299999841) ^ 6948640 = ((209161787 : ℕ) : ZMod 2299999841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_105032736121 : Nat.Prime 105032736121 := by
  refine lucas_primality 105032736121 (7 : ZMod 105032736121) ?_ (fun q hq hd => ?_)
  · rw [show 105032736121 - 1 = 105032736120 from by norm_num]
    reduce_mod_char
  · have e : 105032736121 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 13 ^ 2, 113 ^ 1, 45833 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105032736121 - 1) / 2 = 52516368060 from by norm_num]
      have h2 : (7 : ZMod 105032736121) ^ 52516368060 = ((105032736120 : ℕ) : ZMod 105032736121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105032736121 - 1) / 3 = 35010912040 from by norm_num]
      have h2 : (7 : ZMod 105032736121) ^ 35010912040 = ((64100996678 : ℕ) : ZMod 105032736121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105032736121 - 1) / 5 = 21006547224 from by norm_num]
      have h2 : (7 : ZMod 105032736121) ^ 21006547224 = ((13591603281 : ℕ) : ZMod 105032736121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105032736121 - 1) / 13 = 8079441240 from by norm_num]
      have h2 : (7 : ZMod 105032736121) ^ 8079441240 = ((12939227446 : ℕ) : ZMod 105032736121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105032736121 - 1) / 113 = 929493240 from by norm_num]
      have h2 : (7 : ZMod 105032736121) ^ 929493240 = ((50415233871 : ℕ) : ZMod 105032736121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105032736121 - 1) / 45833 = 2291640 from by norm_num]
      have h2 : (7 : ZMod 105032736121) ^ 2291640 = ((101841513959 : ℕ) : ZMod 105032736121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2653804721 : Nat.Prime 2653804721 := by
  refine lucas_primality 2653804721 (6 : ZMod 2653804721) ?_ (fun q hq hd => ?_)
  · rw [show 2653804721 - 1 = 2653804720 from by norm_num]
    reduce_mod_char
  · have e : 2653804721 - 1 = [2 ^ 4, 5 ^ 1, 7 ^ 3, 17 ^ 1, 5689 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2653804721 - 1) / 2 = 1326902360 from by norm_num]
      have h2 : (6 : ZMod 2653804721) ^ 1326902360 = ((2653804720 : ℕ) : ZMod 2653804721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2653804721 - 1) / 5 = 530760944 from by norm_num]
      have h2 : (6 : ZMod 2653804721) ^ 530760944 = ((278164590 : ℕ) : ZMod 2653804721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2653804721 - 1) / 7 = 379114960 from by norm_num]
      have h2 : (6 : ZMod 2653804721) ^ 379114960 = ((401423688 : ℕ) : ZMod 2653804721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2653804721 - 1) / 17 = 156106160 from by norm_num]
      have h2 : (6 : ZMod 2653804721) ^ 156106160 = ((2113087339 : ℕ) : ZMod 2653804721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2653804721 - 1) / 5689 = 466480 from by norm_num]
      have h2 : (6 : ZMod 2653804721) ^ 466480 = ((2171433535 : ℕ) : ZMod 2653804721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_120737471401 : Nat.Prime 120737471401 := by
  refine lucas_primality 120737471401 (11 : ZMod 120737471401) ?_ (fun q hq hd => ?_)
  · rw [show 120737471401 - 1 = 120737471400 from by norm_num]
    reduce_mod_char
  · have e : 120737471401 - 1 = [2 ^ 3, 3 ^ 3, 5 ^ 2, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 149 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (120737471401 - 1) / 2 = 60368735700 from by norm_num]
      have h2 : (11 : ZMod 120737471401) ^ 60368735700 = ((120737471400 : ℕ) : ZMod 120737471401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (120737471401 - 1) / 3 = 40245823800 from by norm_num]
      have h2 : (11 : ZMod 120737471401) ^ 40245823800 = ((56118750028 : ℕ) : ZMod 120737471401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (120737471401 - 1) / 5 = 24147494280 from by norm_num]
      have h2 : (11 : ZMod 120737471401) ^ 24147494280 = ((14603603865 : ℕ) : ZMod 120737471401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (120737471401 - 1) / 7 = 17248210200 from by norm_num]
      have h2 : (11 : ZMod 120737471401) ^ 17248210200 = ((102117698001 : ℕ) : ZMod 120737471401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (120737471401 - 1) / 13 = 9287497800 from by norm_num]
      have h2 : (11 : ZMod 120737471401) ^ 9287497800 = ((23644392518 : ℕ) : ZMod 120737471401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (120737471401 - 1) / 17 = 7102204200 from by norm_num]
      have h2 : (11 : ZMod 120737471401) ^ 7102204200 = ((57164104274 : ℕ) : ZMod 120737471401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (120737471401 - 1) / 97 = 1244716200 from by norm_num]
      have h2 : (11 : ZMod 120737471401) ^ 1244716200 = ((94006765641 : ℕ) : ZMod 120737471401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (120737471401 - 1) / 149 = 810318600 from by norm_num]
      have h2 : (11 : ZMod 120737471401) ^ 810318600 = ((66865766489 : ℕ) : ZMod 120737471401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_102493609 : Nat.Prime 102493609 := by
  refine lucas_primality 102493609 (23 : ZMod 102493609) ?_ (fun q hq hd => ?_)
  · rw [show 102493609 - 1 = 102493608 from by norm_num]
    reduce_mod_char
  · have e : 102493609 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 610081 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (102493609 - 1) / 2 = 51246804 from by norm_num]
      have h2 : (23 : ZMod 102493609) ^ 51246804 = ((102493608 : ℕ) : ZMod 102493609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (102493609 - 1) / 3 = 34164536 from by norm_num]
      have h2 : (23 : ZMod 102493609) ^ 34164536 = ((245700 : ℕ) : ZMod 102493609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (102493609 - 1) / 7 = 14641944 from by norm_num]
      have h2 : (23 : ZMod 102493609) ^ 14641944 = ((20047500 : ℕ) : ZMod 102493609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (102493609 - 1) / 610081 = 168 from by norm_num]
      have h2 : (23 : ZMod 102493609) ^ 168 = ((79672685 : ℕ) : ZMod 102493609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_133624337761 : Nat.Prime 133624337761 := by
  refine lucas_primality 133624337761 (11 : ZMod 133624337761) ?_ (fun q hq hd => ?_)
  · rw [show 133624337761 - 1 = 133624337760 from by norm_num]
    reduce_mod_char
  · have e : 133624337761 - 1 = [2 ^ 5, 3 ^ 2, 5 ^ 1, 53 ^ 1, 359 ^ 1, 4877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133624337761 - 1) / 2 = 66812168880 from by norm_num]
      have h2 : (11 : ZMod 133624337761) ^ 66812168880 = ((133624337760 : ℕ) : ZMod 133624337761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133624337761 - 1) / 3 = 44541445920 from by norm_num]
      have h2 : (11 : ZMod 133624337761) ^ 44541445920 = ((66525527699 : ℕ) : ZMod 133624337761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133624337761 - 1) / 5 = 26724867552 from by norm_num]
      have h2 : (11 : ZMod 133624337761) ^ 26724867552 = ((132024129634 : ℕ) : ZMod 133624337761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133624337761 - 1) / 53 = 2521213920 from by norm_num]
      have h2 : (11 : ZMod 133624337761) ^ 2521213920 = ((55249080307 : ℕ) : ZMod 133624337761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133624337761 - 1) / 359 = 372212640 from by norm_num]
      have h2 : (11 : ZMod 133624337761) ^ 372212640 = ((73599937998 : ℕ) : ZMod 133624337761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133624337761 - 1) / 4877 = 27398880 from by norm_num]
      have h2 : (11 : ZMod 133624337761) ^ 27398880 = ((132855198872 : ℕ) : ZMod 133624337761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_508142377 : Nat.Prime 508142377 := by
  refine lucas_primality 508142377 (5 : ZMod 508142377) ?_ (fun q hq hd => ?_)
  · rw [show 508142377 - 1 = 508142376 from by norm_num]
    reduce_mod_char
  · have e : 508142377 - 1 = [2 ^ 3, 3 ^ 3, 7 ^ 1, 17 ^ 1, 53 ^ 1, 373 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (508142377 - 1) / 2 = 254071188 from by norm_num]
      have h2 : (5 : ZMod 508142377) ^ 254071188 = ((508142376 : ℕ) : ZMod 508142377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (508142377 - 1) / 3 = 169380792 from by norm_num]
      have h2 : (5 : ZMod 508142377) ^ 169380792 = ((349703995 : ℕ) : ZMod 508142377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (508142377 - 1) / 7 = 72591768 from by norm_num]
      have h2 : (5 : ZMod 508142377) ^ 72591768 = ((388984157 : ℕ) : ZMod 508142377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (508142377 - 1) / 17 = 29890728 from by norm_num]
      have h2 : (5 : ZMod 508142377) ^ 29890728 = ((474728493 : ℕ) : ZMod 508142377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (508142377 - 1) / 53 = 9587592 from by norm_num]
      have h2 : (5 : ZMod 508142377) ^ 9587592 = ((343503581 : ℕ) : ZMod 508142377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (508142377 - 1) / 373 = 1362312 from by norm_num]
      have h2 : (5 : ZMod 508142377) ^ 1362312 = ((498636786 : ℕ) : ZMod 508142377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_167690566321 : Nat.Prime 167690566321 := by
  refine lucas_primality 167690566321 (13 : ZMod 167690566321) ?_ (fun q hq hd => ?_)
  · rw [show 167690566321 - 1 = 167690566320 from by norm_num]
    reduce_mod_char
  · have e : 167690566321 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 17 ^ 1, 19 ^ 1, 127 ^ 1, 17033 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167690566321 - 1) / 2 = 83845283160 from by norm_num]
      have h2 : (13 : ZMod 167690566321) ^ 83845283160 = ((167690566320 : ℕ) : ZMod 167690566321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167690566321 - 1) / 3 = 55896855440 from by norm_num]
      have h2 : (13 : ZMod 167690566321) ^ 55896855440 = ((165859688903 : ℕ) : ZMod 167690566321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167690566321 - 1) / 5 = 33538113264 from by norm_num]
      have h2 : (13 : ZMod 167690566321) ^ 33538113264 = ((108262627595 : ℕ) : ZMod 167690566321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167690566321 - 1) / 17 = 9864150960 from by norm_num]
      have h2 : (13 : ZMod 167690566321) ^ 9864150960 = ((135304276017 : ℕ) : ZMod 167690566321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167690566321 - 1) / 19 = 8825819280 from by norm_num]
      have h2 : (13 : ZMod 167690566321) ^ 8825819280 = ((36963597267 : ℕ) : ZMod 167690566321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167690566321 - 1) / 127 = 1320398160 from by norm_num]
      have h2 : (13 : ZMod 167690566321) ^ 1320398160 = ((32519098391 : ℕ) : ZMod 167690566321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167690566321 - 1) / 17033 = 9845040 from by norm_num]
      have h2 : (13 : ZMod 167690566321) ^ 9845040 = ((68401852656 : ℕ) : ZMod 167690566321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_174853916161 : Nat.Prime 174853916161 := by
  refine lucas_primality 174853916161 (13 : ZMod 174853916161) ?_ (fun q hq hd => ?_)
  · rw [show 174853916161 - 1 = 174853916160 from by norm_num]
    reduce_mod_char
  · have e : 174853916161 - 1 = [2 ^ 9, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 17 ^ 1, 17393 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (174853916161 - 1) / 2 = 87426958080 from by norm_num]
      have h2 : (13 : ZMod 174853916161) ^ 87426958080 = ((174853916160 : ℕ) : ZMod 174853916161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (174853916161 - 1) / 3 = 58284638720 from by norm_num]
      have h2 : (13 : ZMod 174853916161) ^ 58284638720 = ((52511713674 : ℕ) : ZMod 174853916161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (174853916161 - 1) / 5 = 34970783232 from by norm_num]
      have h2 : (13 : ZMod 174853916161) ^ 34970783232 = ((1740862814 : ℕ) : ZMod 174853916161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (174853916161 - 1) / 7 = 24979130880 from by norm_num]
      have h2 : (13 : ZMod 174853916161) ^ 24979130880 = ((83883257870 : ℕ) : ZMod 174853916161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (174853916161 - 1) / 11 = 15895810560 from by norm_num]
      have h2 : (13 : ZMod 174853916161) ^ 15895810560 = ((66490199803 : ℕ) : ZMod 174853916161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (174853916161 - 1) / 17 = 10285524480 from by norm_num]
      have h2 : (13 : ZMod 174853916161) ^ 10285524480 = ((33026490308 : ℕ) : ZMod 174853916161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (174853916161 - 1) / 17393 = 10053120 from by norm_num]
      have h2 : (13 : ZMod 174853916161) ^ 10053120 = ((56491543851 : ℕ) : ZMod 174853916161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_216298456921 : Nat.Prime 216298456921 := by
  refine lucas_primality 216298456921 (11 : ZMod 216298456921) ?_ (fun q hq hd => ?_)
  · rw [show 216298456921 - 1 = 216298456920 from by norm_num]
    reduce_mod_char
  · have e : 216298456921 - 1 = [2 ^ 3, 3 ^ 4, 5 ^ 1, 7 ^ 1, 13 ^ 1, 29 ^ 1, 41 ^ 1, 617 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216298456921 - 1) / 2 = 108149228460 from by norm_num]
      have h2 : (11 : ZMod 216298456921) ^ 108149228460 = ((216298456920 : ℕ) : ZMod 216298456921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216298456921 - 1) / 3 = 72099485640 from by norm_num]
      have h2 : (11 : ZMod 216298456921) ^ 72099485640 = ((72769590715 : ℕ) : ZMod 216298456921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216298456921 - 1) / 5 = 43259691384 from by norm_num]
      have h2 : (11 : ZMod 216298456921) ^ 43259691384 = ((153556519020 : ℕ) : ZMod 216298456921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216298456921 - 1) / 7 = 30899779560 from by norm_num]
      have h2 : (11 : ZMod 216298456921) ^ 30899779560 = ((160245650214 : ℕ) : ZMod 216298456921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216298456921 - 1) / 13 = 16638342840 from by norm_num]
      have h2 : (11 : ZMod 216298456921) ^ 16638342840 = ((94383726469 : ℕ) : ZMod 216298456921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216298456921 - 1) / 29 = 7458567480 from by norm_num]
      have h2 : (11 : ZMod 216298456921) ^ 7458567480 = ((34030476009 : ℕ) : ZMod 216298456921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216298456921 - 1) / 41 = 5275572120 from by norm_num]
      have h2 : (11 : ZMod 216298456921) ^ 5275572120 = ((35550595489 : ℕ) : ZMod 216298456921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216298456921 - 1) / 617 = 350564760 from by norm_num]
      have h2 : (11 : ZMod 216298456921) ^ 350564760 = ((103231922641 : ℕ) : ZMod 216298456921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_108149228461 : Nat.Prime 108149228461 := by
  refine lucas_primality 108149228461 (26 : ZMod 108149228461) ?_ (fun q hq hd => ?_)
  · rw [show 108149228461 - 1 = 108149228460 from by norm_num]
    reduce_mod_char
  · have e : 108149228461 - 1 = [2 ^ 2, 3 ^ 4, 5 ^ 1, 7 ^ 1, 13 ^ 1, 29 ^ 1, 41 ^ 1, 617 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108149228461 - 1) / 2 = 54074614230 from by norm_num]
      have h2 : (26 : ZMod 108149228461) ^ 54074614230 = ((108149228460 : ℕ) : ZMod 108149228461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108149228461 - 1) / 3 = 36049742820 from by norm_num]
      have h2 : (26 : ZMod 108149228461) ^ 36049742820 = ((108148899600 : ℕ) : ZMod 108149228461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108149228461 - 1) / 5 = 21629845692 from by norm_num]
      have h2 : (26 : ZMod 108149228461) ^ 21629845692 = ((90857307043 : ℕ) : ZMod 108149228461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108149228461 - 1) / 7 = 15449889780 from by norm_num]
      have h2 : (26 : ZMod 108149228461) ^ 15449889780 = ((106885915620 : ℕ) : ZMod 108149228461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108149228461 - 1) / 13 = 8319171420 from by norm_num]
      have h2 : (26 : ZMod 108149228461) ^ 8319171420 = ((94167510728 : ℕ) : ZMod 108149228461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108149228461 - 1) / 29 = 3729283740 from by norm_num]
      have h2 : (26 : ZMod 108149228461) ^ 3729283740 = ((64602400498 : ℕ) : ZMod 108149228461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108149228461 - 1) / 41 = 2637786060 from by norm_num]
      have h2 : (26 : ZMod 108149228461) ^ 2637786060 = ((77144705823 : ℕ) : ZMod 108149228461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108149228461 - 1) / 617 = 175282380 from by norm_num]
      have h2 : (26 : ZMod 108149228461) ^ 175282380 = ((58223519070 : ℕ) : ZMod 108149228461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_227165634841 : Nat.Prime 227165634841 := by
  refine lucas_primality 227165634841 (7 : ZMod 227165634841) ?_ (fun q hq hd => ?_)
  · rw [show 227165634841 - 1 = 227165634840 from by norm_num]
    reduce_mod_char
  · have e : 227165634841 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 41 ^ 1, 137 ^ 1, 337021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227165634841 - 1) / 2 = 113582817420 from by norm_num]
      have h2 : (7 : ZMod 227165634841) ^ 113582817420 = ((227165634840 : ℕ) : ZMod 227165634841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227165634841 - 1) / 3 = 75721878280 from by norm_num]
      have h2 : (7 : ZMod 227165634841) ^ 75721878280 = ((99665459388 : ℕ) : ZMod 227165634841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227165634841 - 1) / 5 = 45433126968 from by norm_num]
      have h2 : (7 : ZMod 227165634841) ^ 45433126968 = ((132961679623 : ℕ) : ZMod 227165634841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227165634841 - 1) / 41 = 5540625240 from by norm_num]
      have h2 : (7 : ZMod 227165634841) ^ 5540625240 = ((82170236066 : ℕ) : ZMod 227165634841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227165634841 - 1) / 137 = 1658143320 from by norm_num]
      have h2 : (7 : ZMod 227165634841) ^ 1658143320 = ((90564388747 : ℕ) : ZMod 227165634841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227165634841 - 1) / 337021 = 674040 from by norm_num]
      have h2 : (7 : ZMod 227165634841) ^ 674040 = ((1636870653 : ℕ) : ZMod 227165634841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_236150096041 : Nat.Prime 236150096041 := by
  refine lucas_primality 236150096041 (13 : ZMod 236150096041) ?_ (fun q hq hd => ?_)
  · rw [show 236150096041 - 1 = 236150096040 from by norm_num]
    reduce_mod_char
  · have e : 236150096041 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 17 ^ 2, 23 ^ 1, 29 ^ 1, 41 ^ 1, 83 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236150096041 - 1) / 2 = 118075048020 from by norm_num]
      have h2 : (13 : ZMod 236150096041) ^ 118075048020 = ((236150096040 : ℕ) : ZMod 236150096041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236150096041 - 1) / 3 = 78716698680 from by norm_num]
      have h2 : (13 : ZMod 236150096041) ^ 78716698680 = ((181083844733 : ℕ) : ZMod 236150096041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236150096041 - 1) / 5 = 47230019208 from by norm_num]
      have h2 : (13 : ZMod 236150096041) ^ 47230019208 = ((206660622625 : ℕ) : ZMod 236150096041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236150096041 - 1) / 17 = 13891182120 from by norm_num]
      have h2 : (13 : ZMod 236150096041) ^ 13891182120 = ((45482106876 : ℕ) : ZMod 236150096041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236150096041 - 1) / 23 = 10267395480 from by norm_num]
      have h2 : (13 : ZMod 236150096041) ^ 10267395480 = ((23232267673 : ℕ) : ZMod 236150096041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236150096041 - 1) / 29 = 8143106760 from by norm_num]
      have h2 : (13 : ZMod 236150096041) ^ 8143106760 = ((64136914161 : ℕ) : ZMod 236150096041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236150096041 - 1) / 41 = 5759758440 from by norm_num]
      have h2 : (13 : ZMod 236150096041) ^ 5759758440 = ((207666301599 : ℕ) : ZMod 236150096041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236150096041 - 1) / 83 = 2845181880 from by norm_num]
      have h2 : (13 : ZMod 236150096041) ^ 2845181880 = ((111844833256 : ℕ) : ZMod 236150096041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16867864003 : Nat.Prime 16867864003 := by
  refine lucas_primality 16867864003 (2 : ZMod 16867864003) ?_ (fun q hq hd => ?_)
  · rw [show 16867864003 - 1 = 16867864002 from by norm_num]
    reduce_mod_char
  · have e : 16867864003 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 15619 ^ 1, 16363 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16867864003 - 1) / 2 = 8433932001 from by norm_num]
      have h2 : (2 : ZMod 16867864003) ^ 8433932001 = ((16867864002 : ℕ) : ZMod 16867864003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16867864003 - 1) / 3 = 5622621334 from by norm_num]
      have h2 : (2 : ZMod 16867864003) ^ 5622621334 = ((16867520382 : ℕ) : ZMod 16867864003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16867864003 - 1) / 11 = 1533442182 from by norm_num]
      have h2 : (2 : ZMod 16867864003) ^ 1533442182 = ((4974532399 : ℕ) : ZMod 16867864003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16867864003 - 1) / 15619 = 1079958 from by norm_num]
      have h2 : (2 : ZMod 16867864003) ^ 1079958 = ((16417631392 : ℕ) : ZMod 16867864003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16867864003 - 1) / 16363 = 1030854 from by norm_num]
      have h2 : (2 : ZMod 16867864003) ^ 1030854 = ((16314451213 : ℕ) : ZMod 16867864003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_221945579 : Nat.Prime 221945579 := by
  refine lucas_primality 221945579 (2 : ZMod 221945579) ?_ (fun q hq hd => ?_)
  · rw [show 221945579 - 1 = 221945578 from by norm_num]
    reduce_mod_char
  · have e : 221945579 - 1 = [2 ^ 1, 1627 ^ 1, 68207 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (221945579 - 1) / 2 = 110972789 from by norm_num]
      have h2 : (2 : ZMod 221945579) ^ 110972789 = ((221945578 : ℕ) : ZMod 221945579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (221945579 - 1) / 1627 = 136414 from by norm_num]
      have h2 : (2 : ZMod 221945579) ^ 136414 = ((45703460 : ℕ) : ZMod 221945579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (221945579 - 1) / 68207 = 3254 from by norm_num]
      have h2 : (2 : ZMod 221945579) ^ 3254 = ((198941438 : ℕ) : ZMod 221945579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_269707666801 : Nat.Prime 269707666801 := by
  refine lucas_primality 269707666801 (7 : ZMod 269707666801) ?_ (fun q hq hd => ?_)
  · rw [show 269707666801 - 1 = 269707666800 from by norm_num]
    reduce_mod_char
  · have e : 269707666801 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 11 ^ 1, 13 ^ 1, 37 ^ 1, 107 ^ 1, 397 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269707666801 - 1) / 2 = 134853833400 from by norm_num]
      have h2 : (7 : ZMod 269707666801) ^ 134853833400 = ((269707666800 : ℕ) : ZMod 269707666801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269707666801 - 1) / 3 = 89902555600 from by norm_num]
      have h2 : (7 : ZMod 269707666801) ^ 89902555600 = ((193002753067 : ℕ) : ZMod 269707666801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269707666801 - 1) / 5 = 53941533360 from by norm_num]
      have h2 : (7 : ZMod 269707666801) ^ 53941533360 = ((29878962341 : ℕ) : ZMod 269707666801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269707666801 - 1) / 11 = 24518878800 from by norm_num]
      have h2 : (7 : ZMod 269707666801) ^ 24518878800 = ((250834313870 : ℕ) : ZMod 269707666801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269707666801 - 1) / 13 = 20746743600 from by norm_num]
      have h2 : (7 : ZMod 269707666801) ^ 20746743600 = ((130112075722 : ℕ) : ZMod 269707666801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269707666801 - 1) / 37 = 7289396400 from by norm_num]
      have h2 : (7 : ZMod 269707666801) ^ 7289396400 = ((92221508854 : ℕ) : ZMod 269707666801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269707666801 - 1) / 107 = 2520632400 from by norm_num]
      have h2 : (7 : ZMod 269707666801) ^ 2520632400 = ((14660712548 : ℕ) : ZMod 269707666801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269707666801 - 1) / 397 = 679364400 from by norm_num]
      have h2 : (7 : ZMod 269707666801) ^ 679364400 = ((185399434549 : ℕ) : ZMod 269707666801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_356641641361 : Nat.Prime 356641641361 := by
  refine lucas_primality 356641641361 (21 : ZMod 356641641361) ?_ (fun q hq hd => ?_)
  · rw [show 356641641361 - 1 = 356641641360 from by norm_num]
    reduce_mod_char
  · have e : 356641641361 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 17 ^ 1, 23 ^ 1, 37 ^ 1, 101 ^ 1, 113 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (356641641361 - 1) / 2 = 178320820680 from by norm_num]
      have h2 : (21 : ZMod 356641641361) ^ 178320820680 = ((356641641360 : ℕ) : ZMod 356641641361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (356641641361 - 1) / 3 = 118880547120 from by norm_num]
      have h2 : (21 : ZMod 356641641361) ^ 118880547120 = ((118211025741 : ℕ) : ZMod 356641641361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (356641641361 - 1) / 5 = 71328328272 from by norm_num]
      have h2 : (21 : ZMod 356641641361) ^ 71328328272 = ((113793225064 : ℕ) : ZMod 356641641361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (356641641361 - 1) / 17 = 20978920080 from by norm_num]
      have h2 : (21 : ZMod 356641641361) ^ 20978920080 = ((235562216329 : ℕ) : ZMod 356641641361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (356641641361 - 1) / 23 = 15506158320 from by norm_num]
      have h2 : (21 : ZMod 356641641361) ^ 15506158320 = ((198508218547 : ℕ) : ZMod 356641641361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (356641641361 - 1) / 37 = 9638963280 from by norm_num]
      have h2 : (21 : ZMod 356641641361) ^ 9638963280 = ((285850815602 : ℕ) : ZMod 356641641361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (356641641361 - 1) / 101 = 3531105360 from by norm_num]
      have h2 : (21 : ZMod 356641641361) ^ 3531105360 = ((192627963090 : ℕ) : ZMod 356641641361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (356641641361 - 1) / 113 = 3156120720 from by norm_num]
      have h2 : (21 : ZMod 356641641361) ^ 3156120720 = ((226629433147 : ℕ) : ZMod 356641641361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_494026946041 : Nat.Prime 494026946041 := by
  refine lucas_primality 494026946041 (13 : ZMod 494026946041) ?_ (fun q hq hd => ?_)
  · rw [show 494026946041 - 1 = 494026946040 from by norm_num]
    reduce_mod_char
  · have e : 494026946041 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 83 ^ 1, 499 ^ 1, 99401 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (494026946041 - 1) / 2 = 247013473020 from by norm_num]
      have h2 : (13 : ZMod 494026946041) ^ 247013473020 = ((494026946040 : ℕ) : ZMod 494026946041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (494026946041 - 1) / 3 = 164675648680 from by norm_num]
      have h2 : (13 : ZMod 494026946041) ^ 164675648680 = ((119446031976 : ℕ) : ZMod 494026946041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (494026946041 - 1) / 5 = 98805389208 from by norm_num]
      have h2 : (13 : ZMod 494026946041) ^ 98805389208 = ((138092188207 : ℕ) : ZMod 494026946041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (494026946041 - 1) / 83 = 5952131880 from by norm_num]
      have h2 : (13 : ZMod 494026946041) ^ 5952131880 = ((438915559372 : ℕ) : ZMod 494026946041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (494026946041 - 1) / 499 = 990033960 from by norm_num]
      have h2 : (13 : ZMod 494026946041) ^ 990033960 = ((64662318363 : ℕ) : ZMod 494026946041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (494026946041 - 1) / 99401 = 4970040 from by norm_num]
      have h2 : (13 : ZMod 494026946041) ^ 4970040 = ((357462973389 : ℕ) : ZMod 494026946041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_526511408281 : Nat.Prime 526511408281 := by
  refine lucas_primality 526511408281 (7 : ZMod 526511408281) ?_ (fun q hq hd => ?_)
  · rw [show 526511408281 - 1 = 526511408280 from by norm_num]
    reduce_mod_char
  · have e : 526511408281 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 11 ^ 1, 13 ^ 2, 23 ^ 1, 89 ^ 1, 1153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (526511408281 - 1) / 2 = 263255704140 from by norm_num]
      have h2 : (7 : ZMod 526511408281) ^ 263255704140 = ((526511408280 : ℕ) : ZMod 526511408281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (526511408281 - 1) / 3 = 175503802760 from by norm_num]
      have h2 : (7 : ZMod 526511408281) ^ 175503802760 = ((154623905543 : ℕ) : ZMod 526511408281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (526511408281 - 1) / 5 = 105302281656 from by norm_num]
      have h2 : (7 : ZMod 526511408281) ^ 105302281656 = ((200117624495 : ℕ) : ZMod 526511408281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (526511408281 - 1) / 11 = 47864673480 from by norm_num]
      have h2 : (7 : ZMod 526511408281) ^ 47864673480 = ((427542609473 : ℕ) : ZMod 526511408281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (526511408281 - 1) / 13 = 40500877560 from by norm_num]
      have h2 : (7 : ZMod 526511408281) ^ 40500877560 = ((324377235189 : ℕ) : ZMod 526511408281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (526511408281 - 1) / 23 = 22891800360 from by norm_num]
      have h2 : (7 : ZMod 526511408281) ^ 22891800360 = ((208721247822 : ℕ) : ZMod 526511408281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (526511408281 - 1) / 89 = 5915858520 from by norm_num]
      have h2 : (7 : ZMod 526511408281) ^ 5915858520 = ((396711880047 : ℕ) : ZMod 526511408281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (526511408281 - 1) / 1153 = 456644760 from by norm_num]
      have h2 : (7 : ZMod 526511408281) ^ 456644760 = ((486969916820 : ℕ) : ZMod 526511408281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4315667281 : Nat.Prime 4315667281 := by
  refine lucas_primality 4315667281 (22 : ZMod 4315667281) ?_ (fun q hq hd => ?_)
  · rw [show 4315667281 - 1 = 4315667280 from by norm_num]
    reduce_mod_char
  · have e : 4315667281 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 17981947 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4315667281 - 1) / 2 = 2157833640 from by norm_num]
      have h2 : (22 : ZMod 4315667281) ^ 2157833640 = ((4315667280 : ℕ) : ZMod 4315667281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4315667281 - 1) / 3 = 1438555760 from by norm_num]
      have h2 : (22 : ZMod 4315667281) ^ 1438555760 = ((513084 : ℕ) : ZMod 4315667281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4315667281 - 1) / 5 = 863133456 from by norm_num]
      have h2 : (22 : ZMod 4315667281) ^ 863133456 = ((3363138586 : ℕ) : ZMod 4315667281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4315667281 - 1) / 17981947 = 240 from by norm_num]
      have h2 : (22 : ZMod 4315667281) ^ 240 = ((3498699268 : ℕ) : ZMod 4315667281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2157833641 : Nat.Prime 2157833641 := by
  refine lucas_primality 2157833641 (7 : ZMod 2157833641) ?_ (fun q hq hd => ?_)
  · rw [show 2157833641 - 1 = 2157833640 from by norm_num]
    reduce_mod_char
  · have e : 2157833641 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 17981947 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2157833641 - 1) / 2 = 1078916820 from by norm_num]
      have h2 : (7 : ZMod 2157833641) ^ 1078916820 = ((2157833640 : ℕ) : ZMod 2157833641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2157833641 - 1) / 3 = 719277880 from by norm_num]
      have h2 : (7 : ZMod 2157833641) ^ 719277880 = ((2142701034 : ℕ) : ZMod 2157833641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2157833641 - 1) / 5 = 431566728 from by norm_num]
      have h2 : (7 : ZMod 2157833641) ^ 431566728 = ((67915642 : ℕ) : ZMod 2157833641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2157833641 - 1) / 17981947 = 120 from by norm_num]
      have h2 : (7 : ZMod 2157833641) ^ 120 = ((1766873584 : ℕ) : ZMod 2157833641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_605441180401 : Nat.Prime 605441180401 := by
  refine lucas_primality 605441180401 (26 : ZMod 605441180401) ?_ (fun q hq hd => ?_)
  · rw [show 605441180401 - 1 = 605441180400 from by norm_num]
    reduce_mod_char
  · have e : 605441180401 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 7 ^ 1, 73 ^ 1, 131 ^ 1, 7537 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (605441180401 - 1) / 2 = 302720590200 from by norm_num]
      have h2 : (26 : ZMod 605441180401) ^ 302720590200 = ((605441180400 : ℕ) : ZMod 605441180401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (605441180401 - 1) / 3 = 201813726800 from by norm_num]
      have h2 : (26 : ZMod 605441180401) ^ 201813726800 = ((176453642356 : ℕ) : ZMod 605441180401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (605441180401 - 1) / 5 = 121088236080 from by norm_num]
      have h2 : (26 : ZMod 605441180401) ^ 121088236080 = ((538898756851 : ℕ) : ZMod 605441180401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (605441180401 - 1) / 7 = 86491597200 from by norm_num]
      have h2 : (26 : ZMod 605441180401) ^ 86491597200 = ((411266134573 : ℕ) : ZMod 605441180401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (605441180401 - 1) / 73 = 8293714800 from by norm_num]
      have h2 : (26 : ZMod 605441180401) ^ 8293714800 = ((158140174531 : ℕ) : ZMod 605441180401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (605441180401 - 1) / 131 = 4621688400 from by norm_num]
      have h2 : (26 : ZMod 605441180401) ^ 4621688400 = ((335299095403 : ℕ) : ZMod 605441180401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (605441180401 - 1) / 7537 = 80329200 from by norm_num]
      have h2 : (26 : ZMod 605441180401) ^ 80329200 = ((140032745741 : ℕ) : ZMod 605441180401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8181637573 : Nat.Prime 8181637573 := by
  refine lucas_primality 8181637573 (2 : ZMod 8181637573) ?_ (fun q hq hd => ?_)
  · rw [show 8181637573 - 1 = 8181637572 from by norm_num]
    reduce_mod_char
  · have e : 8181637573 - 1 = [2 ^ 2, 3 ^ 1, 71 ^ 1, 9602861 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8181637573 - 1) / 2 = 4090818786 from by norm_num]
      have h2 : (2 : ZMod 8181637573) ^ 4090818786 = ((8181637572 : ℕ) : ZMod 8181637573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8181637573 - 1) / 3 = 2727212524 from by norm_num]
      have h2 : (2 : ZMod 8181637573) ^ 2727212524 = ((550200 : ℕ) : ZMod 8181637573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8181637573 - 1) / 71 = 115234332 from by norm_num]
      have h2 : (2 : ZMod 8181637573) ^ 115234332 = ((4850906403 : ℕ) : ZMod 8181637573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8181637573 - 1) / 9602861 = 852 from by norm_num]
      have h2 : (2 : ZMod 8181637573) ^ 852 = ((2041741986 : ℕ) : ZMod 8181637573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_698052650881 : Nat.Prime 698052650881 := by
  refine lucas_primality 698052650881 (14 : ZMod 698052650881) ?_ (fun q hq hd => ?_)
  · rw [show 698052650881 - 1 = 698052650880 from by norm_num]
    reduce_mod_char
  · have e : 698052650881 - 1 = [2 ^ 7, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 61 ^ 1, 149 ^ 1, 181 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (698052650881 - 1) / 2 = 349026325440 from by norm_num]
      have h2 : (14 : ZMod 698052650881) ^ 349026325440 = ((698052650880 : ℕ) : ZMod 698052650881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (698052650881 - 1) / 3 = 232684216960 from by norm_num]
      have h2 : (14 : ZMod 698052650881) ^ 232684216960 = ((57538945511 : ℕ) : ZMod 698052650881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (698052650881 - 1) / 5 = 139610530176 from by norm_num]
      have h2 : (14 : ZMod 698052650881) ^ 139610530176 = ((626602157324 : ℕ) : ZMod 698052650881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (698052650881 - 1) / 13 = 53696357760 from by norm_num]
      have h2 : (14 : ZMod 698052650881) ^ 53696357760 = ((549663339026 : ℕ) : ZMod 698052650881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (698052650881 - 1) / 17 = 41061920640 from by norm_num]
      have h2 : (14 : ZMod 698052650881) ^ 41061920640 = ((348077357655 : ℕ) : ZMod 698052650881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (698052650881 - 1) / 61 = 11443486080 from by norm_num]
      have h2 : (14 : ZMod 698052650881) ^ 11443486080 = ((675614498448 : ℕ) : ZMod 698052650881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (698052650881 - 1) / 149 = 4684917120 from by norm_num]
      have h2 : (14 : ZMod 698052650881) ^ 4684917120 = ((295674559138 : ℕ) : ZMod 698052650881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (698052650881 - 1) / 181 = 3856644480 from by norm_num]
      have h2 : (14 : ZMod 698052650881) ^ 3856644480 = ((112726870790 : ℕ) : ZMod 698052650881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17404710161 : Nat.Prime 17404710161 := by
  refine lucas_primality 17404710161 (3 : ZMod 17404710161) ?_ (fun q hq hd => ?_)
  · rw [show 17404710161 - 1 = 17404710160 from by norm_num]
    reduce_mod_char
  · have e : 17404710161 - 1 = [2 ^ 4, 5 ^ 1, 17 ^ 1, 109 ^ 1, 137 ^ 1, 857 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17404710161 - 1) / 2 = 8702355080 from by norm_num]
      have h2 : (3 : ZMod 17404710161) ^ 8702355080 = ((17404710160 : ℕ) : ZMod 17404710161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17404710161 - 1) / 5 = 3480942032 from by norm_num]
      have h2 : (3 : ZMod 17404710161) ^ 3480942032 = ((15406556026 : ℕ) : ZMod 17404710161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17404710161 - 1) / 17 = 1023806480 from by norm_num]
      have h2 : (3 : ZMod 17404710161) ^ 1023806480 = ((6526668238 : ℕ) : ZMod 17404710161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17404710161 - 1) / 109 = 159676240 from by norm_num]
      have h2 : (3 : ZMod 17404710161) ^ 159676240 = ((9270547567 : ℕ) : ZMod 17404710161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17404710161 - 1) / 137 = 127041680 from by norm_num]
      have h2 : (3 : ZMod 17404710161) ^ 127041680 = ((10893772687 : ℕ) : ZMod 17404710161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17404710161 - 1) / 857 = 20308880 from by norm_num]
      have h2 : (3 : ZMod 17404710161) ^ 20308880 = ((8814313954 : ℕ) : ZMod 17404710161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_795223177321 : Nat.Prime 795223177321 := by
  refine lucas_primality 795223177321 (14 : ZMod 795223177321) ?_ (fun q hq hd => ?_)
  · rw [show 795223177321 - 1 = 795223177320 from by norm_num]
    reduce_mod_char
  · have e : 795223177321 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 89 ^ 1, 109 ^ 1, 281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 2 = 397611588660 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 397611588660 = ((795223177320 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 3 = 265074392440 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 265074392440 = ((448637193877 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 5 = 159044635464 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 159044635464 = ((99059992859 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 11 = 72293016120 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 72293016120 = ((100605487971 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 13 = 61171013640 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 61171013640 = ((86950018035 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 17 = 46777833960 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 46777833960 = ((201910214661 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 89 = 8935091880 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 8935091880 = ((485000882497 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 109 = 7295625480 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 7295625480 = ((624556184005 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (795223177321 - 1) / 281 = 2829975720 from by norm_num]
      have h2 : (14 : ZMod 795223177321) ^ 2829975720 = ((229631560857 : ℕ) : ZMod 795223177321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_914721449881 : Nat.Prime 914721449881 := by
  refine lucas_primality 914721449881 (11 : ZMod 914721449881) ?_ (fun q hq hd => ?_)
  · rw [show 914721449881 - 1 = 914721449880 from by norm_num]
    reduce_mod_char
  · have e : 914721449881 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 7 ^ 1, 83 ^ 1, 97 ^ 1, 135257 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (914721449881 - 1) / 2 = 457360724940 from by norm_num]
      have h2 : (11 : ZMod 914721449881) ^ 457360724940 = ((914721449880 : ℕ) : ZMod 914721449881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (914721449881 - 1) / 3 = 304907149960 from by norm_num]
      have h2 : (11 : ZMod 914721449881) ^ 304907149960 = ((294949339752 : ℕ) : ZMod 914721449881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (914721449881 - 1) / 5 = 182944289976 from by norm_num]
      have h2 : (11 : ZMod 914721449881) ^ 182944289976 = ((116996021712 : ℕ) : ZMod 914721449881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (914721449881 - 1) / 7 = 130674492840 from by norm_num]
      have h2 : (11 : ZMod 914721449881) ^ 130674492840 = ((298796574176 : ℕ) : ZMod 914721449881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (914721449881 - 1) / 83 = 11020740360 from by norm_num]
      have h2 : (11 : ZMod 914721449881) ^ 11020740360 = ((148363720887 : ℕ) : ZMod 914721449881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (914721449881 - 1) / 97 = 9430118040 from by norm_num]
      have h2 : (11 : ZMod 914721449881) ^ 9430118040 = ((181909896290 : ℕ) : ZMod 914721449881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (914721449881 - 1) / 135257 = 6762840 from by norm_num]
      have h2 : (11 : ZMod 914721449881) ^ 6762840 = ((364739052301 : ℕ) : ZMod 914721449881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_655342169 : Nat.Prime 655342169 := by
  refine lucas_primality 655342169 (3 : ZMod 655342169) ?_ (fun q hq hd => ?_)
  · rw [show 655342169 - 1 = 655342168 from by norm_num]
    reduce_mod_char
  · have e : 655342169 - 1 = [2 ^ 3, 13 ^ 1, 2131 ^ 1, 2957 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (655342169 - 1) / 2 = 327671084 from by norm_num]
      have h2 : (3 : ZMod 655342169) ^ 327671084 = ((655342168 : ℕ) : ZMod 655342169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (655342169 - 1) / 13 = 50410936 from by norm_num]
      have h2 : (3 : ZMod 655342169) ^ 50410936 = ((650564391 : ℕ) : ZMod 655342169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (655342169 - 1) / 2131 = 307528 from by norm_num]
      have h2 : (3 : ZMod 655342169) ^ 307528 = ((218130964 : ℕ) : ZMod 655342169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (655342169 - 1) / 2957 = 221624 from by norm_num]
      have h2 : (3 : ZMod 655342169) ^ 221624 = ((557915425 : ℕ) : ZMod 655342169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15728212057 : Nat.Prime 15728212057 := by
  refine lucas_primality 15728212057 (11 : ZMod 15728212057) ?_ (fun q hq hd => ?_)
  · rw [show 15728212057 - 1 = 15728212056 from by norm_num]
    reduce_mod_char
  · have e : 15728212057 - 1 = [2 ^ 3, 3 ^ 1, 655342169 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15728212057 - 1) / 2 = 7864106028 from by norm_num]
      have h2 : (11 : ZMod 15728212057) ^ 7864106028 = ((15728212056 : ℕ) : ZMod 15728212057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15728212057 - 1) / 3 = 5242737352 from by norm_num]
      have h2 : (11 : ZMod 15728212057) ^ 5242737352 = ((1492531705 : ℕ) : ZMod 15728212057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_655342169).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15728212057 - 1) / 655342169 = 24 from by norm_num]
      have h2 : (11 : ZMod 15728212057) ^ 24 = ((13352948258 : ℕ) : ZMod 15728212057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_604931233 : Nat.Prime 604931233 := by
  refine lucas_primality 604931233 (10 : ZMod 604931233) ?_ (fun q hq hd => ?_)
  · rw [show 604931233 - 1 = 604931232 from by norm_num]
    reduce_mod_char
  · have e : 604931233 - 1 = [2 ^ 5, 3 ^ 1, 2131 ^ 1, 2957 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604931233 - 1) / 2 = 302465616 from by norm_num]
      have h2 : (10 : ZMod 604931233) ^ 302465616 = ((604931232 : ℕ) : ZMod 604931233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604931233 - 1) / 3 = 201643744 from by norm_num]
      have h2 : (10 : ZMod 604931233) ^ 201643744 = ((518620725 : ℕ) : ZMod 604931233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604931233 - 1) / 2131 = 283872 from by norm_num]
      have h2 : (10 : ZMod 604931233) ^ 283872 = ((602881224 : ℕ) : ZMod 604931233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604931233 - 1) / 2957 = 204576 from by norm_num]
      have h2 : (10 : ZMod 604931233) ^ 204576 = ((415321536 : ℕ) : ZMod 604931233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1256240888281 : Nat.Prime 1256240888281 := by
  refine lucas_primality 1256240888281 (39 : ZMod 1256240888281) ?_ (fun q hq hd => ?_)
  · rw [show 1256240888281 - 1 = 1256240888280 from by norm_num]
    reduce_mod_char
  · have e : 1256240888281 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 1, 17 ^ 1, 29 ^ 1, 37 ^ 1, 27329 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1256240888281 - 1) / 2 = 628120444140 from by norm_num]
      have h2 : (39 : ZMod 1256240888281) ^ 628120444140 = ((1256240888280 : ℕ) : ZMod 1256240888281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1256240888281 - 1) / 3 = 418746962760 from by norm_num]
      have h2 : (39 : ZMod 1256240888281) ^ 418746962760 = ((453322118927 : ℕ) : ZMod 1256240888281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1256240888281 - 1) / 5 = 251248177656 from by norm_num]
      have h2 : (39 : ZMod 1256240888281) ^ 251248177656 = ((26016801745 : ℕ) : ZMod 1256240888281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1256240888281 - 1) / 7 = 179462984040 from by norm_num]
      have h2 : (39 : ZMod 1256240888281) ^ 179462984040 = ((1105369565017 : ℕ) : ZMod 1256240888281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1256240888281 - 1) / 17 = 73896522840 from by norm_num]
      have h2 : (39 : ZMod 1256240888281) ^ 73896522840 = ((357300493361 : ℕ) : ZMod 1256240888281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1256240888281 - 1) / 29 = 43318651320 from by norm_num]
      have h2 : (39 : ZMod 1256240888281) ^ 43318651320 = ((424555754344 : ℕ) : ZMod 1256240888281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1256240888281 - 1) / 37 = 33952456440 from by norm_num]
      have h2 : (39 : ZMod 1256240888281) ^ 33952456440 = ((228063879709 : ℕ) : ZMod 1256240888281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1256240888281 - 1) / 27329 = 45967320 from by norm_num]
      have h2 : (39 : ZMod 1256240888281) ^ 45967320 = ((659296117530 : ℕ) : ZMod 1256240888281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_42585348521 : Nat.Prime 42585348521 := by
  refine lucas_primality 42585348521 (12 : ZMod 42585348521) ?_ (fun q hq hd => ?_)
  · rw [show 42585348521 - 1 = 42585348520 from by norm_num]
    reduce_mod_char
  · have e : 42585348521 - 1 = [2 ^ 3, 5 ^ 1, 11 ^ 1, 13 ^ 1, 31 ^ 1, 137 ^ 1, 1753 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42585348521 - 1) / 2 = 21292674260 from by norm_num]
      have h2 : (12 : ZMod 42585348521) ^ 21292674260 = ((42585348520 : ℕ) : ZMod 42585348521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42585348521 - 1) / 5 = 8517069704 from by norm_num]
      have h2 : (12 : ZMod 42585348521) ^ 8517069704 = ((33415747908 : ℕ) : ZMod 42585348521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42585348521 - 1) / 11 = 3871395320 from by norm_num]
      have h2 : (12 : ZMod 42585348521) ^ 3871395320 = ((23842982433 : ℕ) : ZMod 42585348521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42585348521 - 1) / 13 = 3275796040 from by norm_num]
      have h2 : (12 : ZMod 42585348521) ^ 3275796040 = ((6715799982 : ℕ) : ZMod 42585348521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42585348521 - 1) / 31 = 1373720920 from by norm_num]
      have h2 : (12 : ZMod 42585348521) ^ 1373720920 = ((4242065954 : ℕ) : ZMod 42585348521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42585348521 - 1) / 137 = 310841960 from by norm_num]
      have h2 : (12 : ZMod 42585348521) ^ 310841960 = ((38610176006 : ℕ) : ZMod 42585348521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42585348521 - 1) / 1753 = 24292840 from by norm_num]
      have h2 : (12 : ZMod 42585348521) ^ 24292840 = ((40175675642 : ℕ) : ZMod 42585348521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1818631539961 : Nat.Prime 1818631539961 := by
  refine lucas_primality 1818631539961 (7 : ZMod 1818631539961) ?_ (fun q hq hd => ?_)
  · rw [show 1818631539961 - 1 = 1818631539960 from by norm_num]
    reduce_mod_char
  · have e : 1818631539961 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 17 ^ 1, 23 ^ 1, 691 ^ 1, 56093 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1818631539961 - 1) / 2 = 909315769980 from by norm_num]
      have h2 : (7 : ZMod 1818631539961) ^ 909315769980 = ((1818631539960 : ℕ) : ZMod 1818631539961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1818631539961 - 1) / 3 = 606210513320 from by norm_num]
      have h2 : (7 : ZMod 1818631539961) ^ 606210513320 = ((855291472404 : ℕ) : ZMod 1818631539961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1818631539961 - 1) / 5 = 363726307992 from by norm_num]
      have h2 : (7 : ZMod 1818631539961) ^ 363726307992 = ((1165846021085 : ℕ) : ZMod 1818631539961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1818631539961 - 1) / 17 = 106978325880 from by norm_num]
      have h2 : (7 : ZMod 1818631539961) ^ 106978325880 = ((1405000486757 : ℕ) : ZMod 1818631539961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1818631539961 - 1) / 23 = 79070936520 from by norm_num]
      have h2 : (7 : ZMod 1818631539961) ^ 79070936520 = ((756984148542 : ℕ) : ZMod 1818631539961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1818631539961 - 1) / 691 = 2631883560 from by norm_num]
      have h2 : (7 : ZMod 1818631539961) ^ 2631883560 = ((1561101569647 : ℕ) : ZMod 1818631539961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1818631539961 - 1) / 56093 = 32421720 from by norm_num]
      have h2 : (7 : ZMod 1818631539961) ^ 32421720 = ((1078413127149 : ℕ) : ZMod 1818631539961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2418436052761 : Nat.Prime 2418436052761 := by
  refine lucas_primality 2418436052761 (29 : ZMod 2418436052761) ?_ (fun q hq hd => ?_)
  · rw [show 2418436052761 - 1 = 2418436052760 from by norm_num]
    reduce_mod_char
  · have e : 2418436052761 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 2, 19 ^ 1, 53 ^ 1, 761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 2 = 1209218026380 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 1209218026380 = ((2418436052760 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 3 = 806145350920 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 806145350920 = ((917090714500 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 5 = 483687210552 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 483687210552 = ((172661496654 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 7 = 345490864680 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 345490864680 = ((1506769552095 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 13 = 186033542520 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 186033542520 = ((939739948461 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 17 = 142260944280 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 142260944280 = ((1394600641699 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 19 = 127286108040 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 127286108040 = ((1936444356121 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 53 = 45630868920 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 45630868920 = ((916835055920 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2418436052761 - 1) / 761 = 3177971160 from by norm_num]
      have h2 : (29 : ZMod 2418436052761) ^ 3177971160 = ((127776207271 : ℕ) : ZMod 2418436052761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_540070579 : Nat.Prime 540070579 := by
  refine lucas_primality 540070579 (2 : ZMod 540070579) ?_ (fun q hq hd => ?_)
  · rw [show 540070579 - 1 = 540070578 from by norm_num]
    reduce_mod_char
  · have e : 540070579 - 1 = [2 ^ 1, 3 ^ 4, 863 ^ 1, 3863 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (540070579 - 1) / 2 = 270035289 from by norm_num]
      have h2 : (2 : ZMod 540070579) ^ 270035289 = ((540070578 : ℕ) : ZMod 540070579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (540070579 - 1) / 3 = 180023526 from by norm_num]
      have h2 : (2 : ZMod 540070579) ^ 180023526 = ((1099644 : ℕ) : ZMod 540070579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (540070579 - 1) / 863 = 625806 from by norm_num]
      have h2 : (2 : ZMod 540070579) ^ 625806 = ((201450503 : ℕ) : ZMod 540070579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (540070579 - 1) / 3863 = 139806 from by norm_num]
      have h2 : (2 : ZMod 540070579) ^ 139806 = ((306356168 : ℕ) : ZMod 540070579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2484329722201 : Nat.Prime 2484329722201 := by
  refine lucas_primality 2484329722201 (11 : ZMod 2484329722201) ?_ (fun q hq hd => ?_)
  · rw [show 2484329722201 - 1 = 2484329722200 from by norm_num]
    reduce_mod_char
  · have e : 2484329722201 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 2, 83 ^ 1, 109 ^ 1, 373 ^ 1, 409 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2484329722201 - 1) / 2 = 1242164861100 from by norm_num]
      have h2 : (11 : ZMod 2484329722201) ^ 1242164861100 = ((2484329722200 : ℕ) : ZMod 2484329722201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2484329722201 - 1) / 3 = 828109907400 from by norm_num]
      have h2 : (11 : ZMod 2484329722201) ^ 828109907400 = ((796008010725 : ℕ) : ZMod 2484329722201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2484329722201 - 1) / 5 = 496865944440 from by norm_num]
      have h2 : (11 : ZMod 2484329722201) ^ 496865944440 = ((936898558862 : ℕ) : ZMod 2484329722201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2484329722201 - 1) / 83 = 29931683400 from by norm_num]
      have h2 : (11 : ZMod 2484329722201) ^ 29931683400 = ((1538312842855 : ℕ) : ZMod 2484329722201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2484329722201 - 1) / 109 = 22792015800 from by norm_num]
      have h2 : (11 : ZMod 2484329722201) ^ 22792015800 = ((1924935090736 : ℕ) : ZMod 2484329722201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2484329722201 - 1) / 373 = 6660401400 from by norm_num]
      have h2 : (11 : ZMod 2484329722201) ^ 6660401400 = ((1980223479297 : ℕ) : ZMod 2484329722201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2484329722201 - 1) / 409 = 6074155800 from by norm_num]
      have h2 : (11 : ZMod 2484329722201) ^ 6074155800 = ((995618272817 : ℕ) : ZMod 2484329722201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_33572023273 : Nat.Prime 33572023273 := by
  refine lucas_primality 33572023273 (5 : ZMod 33572023273) ?_ (fun q hq hd => ?_)
  · rw [show 33572023273 - 1 = 33572023272 from by norm_num]
    reduce_mod_char
  · have e : 33572023273 - 1 = [2 ^ 3, 3 ^ 2, 1163 ^ 1, 400927 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33572023273 - 1) / 2 = 16786011636 from by norm_num]
      have h2 : (5 : ZMod 33572023273) ^ 16786011636 = ((33572023272 : ℕ) : ZMod 33572023273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33572023273 - 1) / 3 = 11190674424 from by norm_num]
      have h2 : (5 : ZMod 33572023273) ^ 11190674424 = ((1114524 : ℕ) : ZMod 33572023273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33572023273 - 1) / 1163 = 28866744 from by norm_num]
      have h2 : (5 : ZMod 33572023273) ^ 28866744 = ((10076661750 : ℕ) : ZMod 33572023273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33572023273 - 1) / 400927 = 83736 from by norm_num]
      have h2 : (5 : ZMod 33572023273) ^ 83736 = ((12946521853 : ℕ) : ZMod 33572023273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3014713114561 : Nat.Prime 3014713114561 := by
  refine lucas_primality 3014713114561 (17 : ZMod 3014713114561) ?_ (fun q hq hd => ?_)
  · rw [show 3014713114561 - 1 = 3014713114560 from by norm_num]
    reduce_mod_char
  · have e : 3014713114561 - 1 = [2 ^ 6, 3 ^ 3, 5 ^ 1, 7 ^ 2, 29 ^ 1, 41 ^ 1, 53 ^ 1, 113 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3014713114561 - 1) / 2 = 1507356557280 from by norm_num]
      have h2 : (17 : ZMod 3014713114561) ^ 1507356557280 = ((3014713114560 : ℕ) : ZMod 3014713114561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3014713114561 - 1) / 3 = 1004904371520 from by norm_num]
      have h2 : (17 : ZMod 3014713114561) ^ 1004904371520 = ((2337523555213 : ℕ) : ZMod 3014713114561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3014713114561 - 1) / 5 = 602942622912 from by norm_num]
      have h2 : (17 : ZMod 3014713114561) ^ 602942622912 = ((1560996029923 : ℕ) : ZMod 3014713114561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3014713114561 - 1) / 7 = 430673302080 from by norm_num]
      have h2 : (17 : ZMod 3014713114561) ^ 430673302080 = ((2494779233935 : ℕ) : ZMod 3014713114561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3014713114561 - 1) / 29 = 103955624640 from by norm_num]
      have h2 : (17 : ZMod 3014713114561) ^ 103955624640 = ((2414760410782 : ℕ) : ZMod 3014713114561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3014713114561 - 1) / 41 = 73529588160 from by norm_num]
      have h2 : (17 : ZMod 3014713114561) ^ 73529588160 = ((520111554854 : ℕ) : ZMod 3014713114561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3014713114561 - 1) / 53 = 56881379520 from by norm_num]
      have h2 : (17 : ZMod 3014713114561) ^ 56881379520 = ((1301076410289 : ℕ) : ZMod 3014713114561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3014713114561 - 1) / 113 = 26678877120 from by norm_num]
      have h2 : (17 : ZMod 3014713114561) ^ 26678877120 = ((1297014155379 : ℕ) : ZMod 3014713114561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3045613188841 : Nat.Prime 3045613188841 := by
  refine lucas_primality 3045613188841 (7 : ZMod 3045613188841) ?_ (fun q hq hd => ?_)
  · rw [show 3045613188841 - 1 = 3045613188840 from by norm_num]
    reduce_mod_char
  · have e : 3045613188841 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 131 ^ 1, 157 ^ 1, 541 ^ 1, 2281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3045613188841 - 1) / 2 = 1522806594420 from by norm_num]
      have h2 : (7 : ZMod 3045613188841) ^ 1522806594420 = ((3045613188840 : ℕ) : ZMod 3045613188841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3045613188841 - 1) / 3 = 1015204396280 from by norm_num]
      have h2 : (7 : ZMod 3045613188841) ^ 1015204396280 = ((1575012122150 : ℕ) : ZMod 3045613188841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3045613188841 - 1) / 5 = 609122637768 from by norm_num]
      have h2 : (7 : ZMod 3045613188841) ^ 609122637768 = ((1573376421535 : ℕ) : ZMod 3045613188841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3045613188841 - 1) / 131 = 23248955640 from by norm_num]
      have h2 : (7 : ZMod 3045613188841) ^ 23248955640 = ((2774160154211 : ℕ) : ZMod 3045613188841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3045613188841 - 1) / 157 = 19398810120 from by norm_num]
      have h2 : (7 : ZMod 3045613188841) ^ 19398810120 = ((2711777007929 : ℕ) : ZMod 3045613188841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3045613188841 - 1) / 541 = 5629599240 from by norm_num]
      have h2 : (7 : ZMod 3045613188841) ^ 5629599240 = ((2014294863820 : ℕ) : ZMod 3045613188841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3045613188841 - 1) / 2281 = 1335209640 from by norm_num]
      have h2 : (7 : ZMod 3045613188841) ^ 1335209640 = ((896722824545 : ℕ) : ZMod 3045613188841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5121667335721 : Nat.Prime 5121667335721 := by
  refine lucas_primality 5121667335721 (7 : ZMod 5121667335721) ?_ (fun q hq hd => ?_)
  · rw [show 5121667335721 - 1 = 5121667335720 from by norm_num]
    reduce_mod_char
  · have e : 5121667335721 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 13 ^ 2, 17 ^ 1, 149 ^ 1, 179 ^ 1, 557 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5121667335721 - 1) / 2 = 2560833667860 from by norm_num]
      have h2 : (7 : ZMod 5121667335721) ^ 2560833667860 = ((5121667335720 : ℕ) : ZMod 5121667335721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5121667335721 - 1) / 3 = 1707222445240 from by norm_num]
      have h2 : (7 : ZMod 5121667335721) ^ 1707222445240 = ((4126370741567 : ℕ) : ZMod 5121667335721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5121667335721 - 1) / 5 = 1024333467144 from by norm_num]
      have h2 : (7 : ZMod 5121667335721) ^ 1024333467144 = ((928360804433 : ℕ) : ZMod 5121667335721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5121667335721 - 1) / 13 = 393974410440 from by norm_num]
      have h2 : (7 : ZMod 5121667335721) ^ 393974410440 = ((4360477829087 : ℕ) : ZMod 5121667335721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5121667335721 - 1) / 17 = 301274549160 from by norm_num]
      have h2 : (7 : ZMod 5121667335721) ^ 301274549160 = ((3795413097413 : ℕ) : ZMod 5121667335721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5121667335721 - 1) / 149 = 34373606280 from by norm_num]
      have h2 : (7 : ZMod 5121667335721) ^ 34373606280 = ((3401760026164 : ℕ) : ZMod 5121667335721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5121667335721 - 1) / 179 = 28612666680 from by norm_num]
      have h2 : (7 : ZMod 5121667335721) ^ 28612666680 = ((3913226772203 : ℕ) : ZMod 5121667335721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5121667335721 - 1) / 557 = 9195093960 from by norm_num]
      have h2 : (7 : ZMod 5121667335721) ^ 9195093960 = ((284467065475 : ℕ) : ZMod 5121667335721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_128304237161 : Nat.Prime 128304237161 := by
  refine lucas_primality 128304237161 (3 : ZMod 128304237161) ?_ (fun q hq hd => ?_)
  · rw [show 128304237161 - 1 = 128304237160 from by norm_num]
    reduce_mod_char
  · have e : 128304237161 - 1 = [2 ^ 3, 5 ^ 1, 11 ^ 1, 29 ^ 1, 31 ^ 1, 324361 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (128304237161 - 1) / 2 = 64152118580 from by norm_num]
      have h2 : (3 : ZMod 128304237161) ^ 64152118580 = ((128304237160 : ℕ) : ZMod 128304237161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (128304237161 - 1) / 5 = 25660847432 from by norm_num]
      have h2 : (3 : ZMod 128304237161) ^ 25660847432 = ((1243338366 : ℕ) : ZMod 128304237161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (128304237161 - 1) / 11 = 11664021560 from by norm_num]
      have h2 : (3 : ZMod 128304237161) ^ 11664021560 = ((79599187519 : ℕ) : ZMod 128304237161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (128304237161 - 1) / 29 = 4424284040 from by norm_num]
      have h2 : (3 : ZMod 128304237161) ^ 4424284040 = ((87383199622 : ℕ) : ZMod 128304237161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (128304237161 - 1) / 31 = 4138846360 from by norm_num]
      have h2 : (3 : ZMod 128304237161) ^ 4138846360 = ((86782678346 : ℕ) : ZMod 128304237161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (128304237161 - 1) / 324361 = 395560 from by norm_num]
      have h2 : (3 : ZMod 128304237161) ^ 395560 = ((39322145646 : ℕ) : ZMod 128304237161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5522257821121 : Nat.Prime 5522257821121 := by
  refine lucas_primality 5522257821121 (29 : ZMod 5522257821121) ?_ (fun q hq hd => ?_)
  · rw [show 5522257821121 - 1 = 5522257821120 from by norm_num]
    reduce_mod_char
  · have e : 5522257821121 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 17 ^ 1, 19 ^ 1, 113 ^ 1, 173 ^ 1, 911 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5522257821121 - 1) / 2 = 2761128910560 from by norm_num]
      have h2 : (29 : ZMod 5522257821121) ^ 2761128910560 = ((5522257821120 : ℕ) : ZMod 5522257821121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5522257821121 - 1) / 3 = 1840752607040 from by norm_num]
      have h2 : (29 : ZMod 5522257821121) ^ 1840752607040 = ((4016351913440 : ℕ) : ZMod 5522257821121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5522257821121 - 1) / 5 = 1104451564224 from by norm_num]
      have h2 : (29 : ZMod 5522257821121) ^ 1104451564224 = ((1707150417587 : ℕ) : ZMod 5522257821121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5522257821121 - 1) / 17 = 324838695360 from by norm_num]
      have h2 : (29 : ZMod 5522257821121) ^ 324838695360 = ((2931689895802 : ℕ) : ZMod 5522257821121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5522257821121 - 1) / 19 = 290645148480 from by norm_num]
      have h2 : (29 : ZMod 5522257821121) ^ 290645148480 = ((869787246877 : ℕ) : ZMod 5522257821121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5522257821121 - 1) / 113 = 48869538240 from by norm_num]
      have h2 : (29 : ZMod 5522257821121) ^ 48869538240 = ((319045898076 : ℕ) : ZMod 5522257821121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5522257821121 - 1) / 173 = 31920565440 from by norm_num]
      have h2 : (29 : ZMod 5522257821121) ^ 31920565440 = ((1770757751080 : ℕ) : ZMod 5522257821121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5522257821121 - 1) / 911 = 6061753920 from by norm_num]
      have h2 : (29 : ZMod 5522257821121) ^ 6061753920 = ((308635930806 : ℕ) : ZMod 5522257821121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_137069088521 : Nat.Prime 137069088521 := by
  refine lucas_primality 137069088521 (3 : ZMod 137069088521) ?_ (fun q hq hd => ?_)
  · rw [show 137069088521 - 1 = 137069088520 from by norm_num]
    reduce_mod_char
  · have e : 137069088521 - 1 = [2 ^ 3, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 37 ^ 1, 131 ^ 1, 457 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137069088521 - 1) / 2 = 68534544260 from by norm_num]
      have h2 : (3 : ZMod 137069088521) ^ 68534544260 = ((137069088520 : ℕ) : ZMod 137069088521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137069088521 - 1) / 5 = 27413817704 from by norm_num]
      have h2 : (3 : ZMod 137069088521) ^ 27413817704 = ((50469911932 : ℕ) : ZMod 137069088521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137069088521 - 1) / 7 = 19581298360 from by norm_num]
      have h2 : (3 : ZMod 137069088521) ^ 19581298360 = ((45813288574 : ℕ) : ZMod 137069088521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137069088521 - 1) / 13 = 10543776040 from by norm_num]
      have h2 : (3 : ZMod 137069088521) ^ 10543776040 = ((54075377779 : ℕ) : ZMod 137069088521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137069088521 - 1) / 17 = 8062887560 from by norm_num]
      have h2 : (3 : ZMod 137069088521) ^ 8062887560 = ((71308578363 : ℕ) : ZMod 137069088521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137069088521 - 1) / 37 = 3704569960 from by norm_num]
      have h2 : (3 : ZMod 137069088521) ^ 3704569960 = ((16888426098 : ℕ) : ZMod 137069088521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137069088521 - 1) / 131 = 1046328920 from by norm_num]
      have h2 : (3 : ZMod 137069088521) ^ 1046328920 = ((103967910740 : ℕ) : ZMod 137069088521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137069088521 - 1) / 457 = 299932360 from by norm_num]
      have h2 : (3 : ZMod 137069088521) ^ 299932360 = ((2235393958 : ℕ) : ZMod 137069088521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19659695017 : Nat.Prime 19659695017 := by
  refine lucas_primality 19659695017 (10 : ZMod 19659695017) ?_ (fun q hq hd => ?_)
  · rw [show 19659695017 - 1 = 19659695016 from by norm_num]
    reduce_mod_char
  · have e : 19659695017 - 1 = [2 ^ 3, 3 ^ 1, 13 ^ 1, 17 ^ 1, 467 ^ 1, 7937 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19659695017 - 1) / 2 = 9829847508 from by norm_num]
      have h2 : (10 : ZMod 19659695017) ^ 9829847508 = ((19659695016 : ℕ) : ZMod 19659695017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19659695017 - 1) / 3 = 6553231672 from by norm_num]
      have h2 : (10 : ZMod 19659695017) ^ 6553231672 = ((17496527515 : ℕ) : ZMod 19659695017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19659695017 - 1) / 13 = 1512284232 from by norm_num]
      have h2 : (10 : ZMod 19659695017) ^ 1512284232 = ((13963291139 : ℕ) : ZMod 19659695017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19659695017 - 1) / 17 = 1156452648 from by norm_num]
      have h2 : (10 : ZMod 19659695017) ^ 1156452648 = ((7786521052 : ℕ) : ZMod 19659695017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19659695017 - 1) / 467 = 42097848 from by norm_num]
      have h2 : (10 : ZMod 19659695017) ^ 42097848 = ((8921413224 : ℕ) : ZMod 19659695017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19659695017 - 1) / 7937 = 2476968 from by norm_num]
      have h2 : (10 : ZMod 19659695017) ^ 2476968 = ((9574536615 : ℕ) : ZMod 19659695017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1029492691 : Nat.Prime 1029492691 := by
  refine lucas_primality 1029492691 (2 : ZMod 1029492691) ?_ (fun q hq hd => ?_)
  · rw [show 1029492691 - 1 = 1029492690 from by norm_num]
    reduce_mod_char
  · have e : 1029492691 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 1319 ^ 1, 26017 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1029492691 - 1) / 2 = 514746345 from by norm_num]
      have h2 : (2 : ZMod 1029492691) ^ 514746345 = ((1029492690 : ℕ) : ZMod 1029492691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1029492691 - 1) / 3 = 343164230 from by norm_num]
      have h2 : (2 : ZMod 1029492691) ^ 343164230 = ((892885877 : ℕ) : ZMod 1029492691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1029492691 - 1) / 5 = 205898538 from by norm_num]
      have h2 : (2 : ZMod 1029492691) ^ 205898538 = ((774348769 : ℕ) : ZMod 1029492691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1029492691 - 1) / 1319 = 780510 from by norm_num]
      have h2 : (2 : ZMod 1029492691) ^ 780510 = ((274789083 : ℕ) : ZMod 1029492691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1029492691 - 1) / 26017 = 39570 from by norm_num]
      have h2 : (2 : ZMod 1029492691) ^ 39570 = ((806971741 : ℕ) : ZMod 1029492691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_98831298337 : Nat.Prime 98831298337 := by
  refine lucas_primality 98831298337 (5 : ZMod 98831298337) ?_ (fun q hq hd => ?_)
  · rw [show 98831298337 - 1 = 98831298336 from by norm_num]
    reduce_mod_char
  · have e : 98831298337 - 1 = [2 ^ 5, 3 ^ 1, 1029492691 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98831298337 - 1) / 2 = 49415649168 from by norm_num]
      have h2 : (5 : ZMod 98831298337) ^ 49415649168 = ((98831298336 : ℕ) : ZMod 98831298337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98831298337 - 1) / 3 = 32943766112 from by norm_num]
      have h2 : (5 : ZMod 98831298337) ^ 32943766112 = ((10012925475 : ℕ) : ZMod 98831298337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1029492691).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98831298337 - 1) / 1029492691 = 96 from by norm_num]
      have h2 : (5 : ZMod 98831298337) ^ 96 = ((52021405651 : ℕ) : ZMod 98831298337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_108062830537 : Nat.Prime 108062830537 := by
  refine lucas_primality 108062830537 (5 : ZMod 108062830537) ?_ (fun q hq hd => ?_)
  · rw [show 108062830537 - 1 = 108062830536 from by norm_num]
    reduce_mod_char
  · have e : 108062830537 - 1 = [2 ^ 3, 3 ^ 1, 30713 ^ 1, 146603 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108062830537 - 1) / 2 = 54031415268 from by norm_num]
      have h2 : (5 : ZMod 108062830537) ^ 54031415268 = ((108062830536 : ℕ) : ZMod 108062830537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108062830537 - 1) / 3 = 36020943512 from by norm_num]
      have h2 : (5 : ZMod 108062830537) ^ 36020943512 = ((75526666051 : ℕ) : ZMod 108062830537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108062830537 - 1) / 30713 = 3518472 from by norm_num]
      have h2 : (5 : ZMod 108062830537) ^ 3518472 = ((99543210816 : ℕ) : ZMod 108062830537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108062830537 - 1) / 146603 = 737112 from by norm_num]
      have h2 : (5 : ZMod 108062830537) ^ 737112 = ((5451162272 : ℕ) : ZMod 108062830537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4156262713 : Nat.Prime 4156262713 := by
  refine lucas_primality 4156262713 (5 : ZMod 4156262713) ?_ (fun q hq hd => ?_)
  · rw [show 4156262713 - 1 = 4156262712 from by norm_num]
    reduce_mod_char
  · have e : 4156262713 - 1 = [2 ^ 3, 3 ^ 3, 7 ^ 3, 56099 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4156262713 - 1) / 2 = 2078131356 from by norm_num]
      have h2 : (5 : ZMod 4156262713) ^ 2078131356 = ((4156262712 : ℕ) : ZMod 4156262713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4156262713 - 1) / 3 = 1385420904 from by norm_num]
      have h2 : (5 : ZMod 4156262713) ^ 1385420904 = ((1187219914 : ℕ) : ZMod 4156262713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4156262713 - 1) / 7 = 593751816 from by norm_num]
      have h2 : (5 : ZMod 4156262713) ^ 593751816 = ((2048342768 : ℕ) : ZMod 4156262713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4156262713 - 1) / 56099 = 74088 from by norm_num]
      have h2 : (5 : ZMod 4156262713) ^ 74088 = ((3032405843 : ℕ) : ZMod 4156262713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8177457331321 : Nat.Prime 8177457331321 := by
  refine lucas_primality 8177457331321 (13 : ZMod 8177457331321) ?_ (fun q hq hd => ?_)
  · rw [show 8177457331321 - 1 = 8177457331320 from by norm_num]
    reduce_mod_char
  · have e : 8177457331321 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 67 ^ 1, 193 ^ 1, 503 ^ 1, 10477 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8177457331321 - 1) / 2 = 4088728665660 from by norm_num]
      have h2 : (13 : ZMod 8177457331321) ^ 4088728665660 = ((8177457331320 : ℕ) : ZMod 8177457331321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8177457331321 - 1) / 3 = 2725819110440 from by norm_num]
      have h2 : (13 : ZMod 8177457331321) ^ 2725819110440 = ((615485657675 : ℕ) : ZMod 8177457331321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8177457331321 - 1) / 5 = 1635491466264 from by norm_num]
      have h2 : (13 : ZMod 8177457331321) ^ 1635491466264 = ((6288126686693 : ℕ) : ZMod 8177457331321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8177457331321 - 1) / 67 = 122051601960 from by norm_num]
      have h2 : (13 : ZMod 8177457331321) ^ 122051601960 = ((1309343380751 : ℕ) : ZMod 8177457331321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8177457331321 - 1) / 193 = 42370245240 from by norm_num]
      have h2 : (13 : ZMod 8177457331321) ^ 42370245240 = ((1435606376231 : ℕ) : ZMod 8177457331321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8177457331321 - 1) / 503 = 16257370440 from by norm_num]
      have h2 : (13 : ZMod 8177457331321) ^ 16257370440 = ((6847311846656 : ℕ) : ZMod 8177457331321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8177457331321 - 1) / 10477 = 780515160 from by norm_num]
      have h2 : (13 : ZMod 8177457331321) ^ 780515160 = ((1138022684820 : ℕ) : ZMod 8177457331321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8642490432721 : Nat.Prime 8642490432721 := by
  refine lucas_primality 8642490432721 (7 : ZMod 8642490432721) ?_ (fun q hq hd => ?_)
  · rw [show 8642490432721 - 1 = 8642490432720 from by norm_num]
    reduce_mod_char
  · have e : 8642490432721 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 17 ^ 1, 853 ^ 1, 1019 ^ 1, 2437 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8642490432721 - 1) / 2 = 4321245216360 from by norm_num]
      have h2 : (7 : ZMod 8642490432721) ^ 4321245216360 = ((8642490432720 : ℕ) : ZMod 8642490432721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8642490432721 - 1) / 3 = 2880830144240 from by norm_num]
      have h2 : (7 : ZMod 8642490432721) ^ 2880830144240 = ((7824501491307 : ℕ) : ZMod 8642490432721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8642490432721 - 1) / 5 = 1728498086544 from by norm_num]
      have h2 : (7 : ZMod 8642490432721) ^ 1728498086544 = ((3590939476706 : ℕ) : ZMod 8642490432721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8642490432721 - 1) / 17 = 508381790160 from by norm_num]
      have h2 : (7 : ZMod 8642490432721) ^ 508381790160 = ((8472404302248 : ℕ) : ZMod 8642490432721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8642490432721 - 1) / 853 = 10131876240 from by norm_num]
      have h2 : (7 : ZMod 8642490432721) ^ 10131876240 = ((5181223049189 : ℕ) : ZMod 8642490432721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8642490432721 - 1) / 1019 = 8481344880 from by norm_num]
      have h2 : (7 : ZMod 8642490432721) ^ 8481344880 = ((5396830748032 : ℕ) : ZMod 8642490432721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8642490432721 - 1) / 2437 = 3546364560 from by norm_num]
      have h2 : (7 : ZMod 8642490432721) ^ 3546364560 = ((4096819334759 : ℕ) : ZMod 8642490432721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116790411253 : Nat.Prime 116790411253 := by
  refine lucas_primality 116790411253 (2 : ZMod 116790411253) ?_ (fun q hq hd => ?_)
  · rw [show 116790411253 - 1 = 116790411252 from by norm_num]
    reduce_mod_char
  · have e : 116790411253 - 1 = [2 ^ 2, 3 ^ 1, 563 ^ 1, 719 ^ 1, 24043 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116790411253 - 1) / 2 = 58395205626 from by norm_num]
      have h2 : (2 : ZMod 116790411253) ^ 58395205626 = ((116790411252 : ℕ) : ZMod 116790411253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116790411253 - 1) / 3 = 38930137084 from by norm_num]
      have h2 : (2 : ZMod 116790411253) ^ 38930137084 = ((116788332492 : ℕ) : ZMod 116790411253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116790411253 - 1) / 563 = 207443004 from by norm_num]
      have h2 : (2 : ZMod 116790411253) ^ 207443004 = ((73743535588 : ℕ) : ZMod 116790411253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116790411253 - 1) / 719 = 162434508 from by norm_num]
      have h2 : (2 : ZMod 116790411253) ^ 162434508 = ((54619149590 : ℕ) : ZMod 116790411253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116790411253 - 1) / 24043 = 4857564 from by norm_num]
      have h2 : (2 : ZMod 116790411253) ^ 4857564 = ((79644313523 : ℕ) : ZMod 116790411253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_216641645201 : Nat.Prime 216641645201 := by
  refine lucas_primality 216641645201 (3 : ZMod 216641645201) ?_ (fun q hq hd => ?_)
  · rw [show 216641645201 - 1 = 216641645200 from by norm_num]
    reduce_mod_char
  · have e : 216641645201 - 1 = [2 ^ 4, 5 ^ 2, 37 ^ 1, 257 ^ 1, 56957 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216641645201 - 1) / 2 = 108320822600 from by norm_num]
      have h2 : (3 : ZMod 216641645201) ^ 108320822600 = ((216641645200 : ℕ) : ZMod 216641645201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216641645201 - 1) / 5 = 43328329040 from by norm_num]
      have h2 : (3 : ZMod 216641645201) ^ 43328329040 = ((156053380030 : ℕ) : ZMod 216641645201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216641645201 - 1) / 37 = 5855179600 from by norm_num]
      have h2 : (3 : ZMod 216641645201) ^ 5855179600 = ((104835881494 : ℕ) : ZMod 216641645201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216641645201 - 1) / 257 = 842963600 from by norm_num]
      have h2 : (3 : ZMod 216641645201) ^ 842963600 = ((46980180584 : ℕ) : ZMod 216641645201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (216641645201 - 1) / 56957 = 3803600 from by norm_num]
      have h2 : (3 : ZMod 216641645201) ^ 3803600 = ((189599908281 : ℕ) : ZMod 216641645201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9162457369561 : Nat.Prime 9162457369561 := by
  refine lucas_primality 9162457369561 (13 : ZMod 9162457369561) ?_ (fun q hq hd => ?_)
  · rw [show 9162457369561 - 1 = 9162457369560 from by norm_num]
    reduce_mod_char
  · have e : 9162457369561 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 11 ^ 1, 23 ^ 1, 47 ^ 1, 157 ^ 1, 13633 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9162457369561 - 1) / 2 = 4581228684780 from by norm_num]
      have h2 : (13 : ZMod 9162457369561) ^ 4581228684780 = ((9162457369560 : ℕ) : ZMod 9162457369561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9162457369561 - 1) / 3 = 3054152456520 from by norm_num]
      have h2 : (13 : ZMod 9162457369561) ^ 3054152456520 = ((8503515316631 : ℕ) : ZMod 9162457369561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9162457369561 - 1) / 5 = 1832491473912 from by norm_num]
      have h2 : (13 : ZMod 9162457369561) ^ 1832491473912 = ((7419618222915 : ℕ) : ZMod 9162457369561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9162457369561 - 1) / 11 = 832950669960 from by norm_num]
      have h2 : (13 : ZMod 9162457369561) ^ 832950669960 = ((5689410979976 : ℕ) : ZMod 9162457369561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9162457369561 - 1) / 23 = 398367711720 from by norm_num]
      have h2 : (13 : ZMod 9162457369561) ^ 398367711720 = ((7307115528217 : ℕ) : ZMod 9162457369561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9162457369561 - 1) / 47 = 194945901480 from by norm_num]
      have h2 : (13 : ZMod 9162457369561) ^ 194945901480 = ((4016557705672 : ℕ) : ZMod 9162457369561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9162457369561 - 1) / 157 = 58359601080 from by norm_num]
      have h2 : (13 : ZMod 9162457369561) ^ 58359601080 = ((7579172260685 : ℕ) : ZMod 9162457369561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9162457369561 - 1) / 13633 = 672079320 from by norm_num]
      have h2 : (13 : ZMod 9162457369561) ^ 672079320 = ((5388637264746 : ℕ) : ZMod 9162457369561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_34445328457 : Nat.Prime 34445328457 := by
  refine lucas_primality 34445328457 (15 : ZMod 34445328457) ?_ (fun q hq hd => ?_)
  · rw [show 34445328457 - 1 = 34445328456 from by norm_num]
    reduce_mod_char
  · have e : 34445328457 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 11 ^ 2, 19 ^ 1, 101 ^ 1, 883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34445328457 - 1) / 2 = 17222664228 from by norm_num]
      have h2 : (15 : ZMod 34445328457) ^ 17222664228 = ((34445328456 : ℕ) : ZMod 34445328457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34445328457 - 1) / 3 = 11481776152 from by norm_num]
      have h2 : (15 : ZMod 34445328457) ^ 11481776152 = ((34443188076 : ℕ) : ZMod 34445328457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34445328457 - 1) / 7 = 4920761208 from by norm_num]
      have h2 : (15 : ZMod 34445328457) ^ 4920761208 = ((6148143601 : ℕ) : ZMod 34445328457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34445328457 - 1) / 11 = 3131393496 from by norm_num]
      have h2 : (15 : ZMod 34445328457) ^ 3131393496 = ((7344258261 : ℕ) : ZMod 34445328457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34445328457 - 1) / 19 = 1812912024 from by norm_num]
      have h2 : (15 : ZMod 34445328457) ^ 1812912024 = ((32060873155 : ℕ) : ZMod 34445328457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34445328457 - 1) / 101 = 341042856 from by norm_num]
      have h2 : (15 : ZMod 34445328457) ^ 341042856 = ((6807349503 : ℕ) : ZMod 34445328457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34445328457 - 1) / 883 = 39009432 from by norm_num]
      have h2 : (15 : ZMod 34445328457) ^ 39009432 = ((20472424941 : ℕ) : ZMod 34445328457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_0 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 7 ≤ z) (hi : z < 300)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 2 = 1 → z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ)) ∧
    (e % 4 = 2 → z ∈ ({11, 139, 181, 199, 271} : Finset ℕ)) ∧
    (e % 8 = 4 → z ∈ ({7, 11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D1 : e % 2 = 1 → 1 + z ^ 1 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D2 : e % 4 = 2 → 1 + z ^ 2 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D4 : e % 8 = 4 → 1 + z ^ 4 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have WK : ∀ L : List ℕ, L.Nodup → (∀ x ∈ L, x ∈ P) →
      2 * L.prod ≤ (L.map (fun p => p + 1)).prod → False := fun L h1 h2 h3 => weight_kill hP E h1 h2 h3
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 7
    · simp
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 7 ^ 2).trans hd)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 11
    · simp
    · simp
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 13
    · simp
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 13 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g14281 := S7 14281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14281 ∣ 1 + 13 ^ 4).trans hd)
      have g193 := S1 193 (by norm_num) (by norm_num) (by decide) 14281 g14281 (by norm_num)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 17
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 17 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 17 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 17 ^ 2).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D4 he
      have g41761 := S7 41761 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41761 ∣ 1 + 17 ^ 4).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 41761 g41761 (by norm_num)
      have g157 := S1 157 (by norm_num) (by norm_num) (by decide) 41761 g41761 (by norm_num)
      have g79 := S1 79 (by norm_num) (by norm_num) (by decide) 157 g157 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 19 g19 79 g79 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 19
    · simp
    · exfalso; have hd := D2 he
      have g181 := S7 181 (by norm_num) (by norm_num) (by decide) ((by norm_num : 181 ∣ 1 + 19 ^ 2).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 181 g181 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 19 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 23
    · simp
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 23 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g139921 := S7 139921 (by norm_num) (by norm_num) (by decide) ((by norm_num : 139921 ∣ 1 + 23 ^ 4).trans hd)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 139921 g139921 (by norm_num)
      have g1627 := S1 1627 (by norm_num) (by norm_num) (by decide) 139921 g139921 (by norm_num)
      exact absurd (S3 11 (by norm_num) (by norm_num) (by decide) 43 g43 1627 g1627 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 29
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 29 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 29 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g421 := S7 421 (by norm_num) (by norm_num) (by decide) ((by norm_num : 421 ∣ 1 + 29 ^ 2).trans hd)
      have g211 := S1 211 (by norm_num) (by norm_num) (by decide) 421 g421 (by norm_num)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 211 g211 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g353641 := S7 353641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353641 ∣ 1 + 29 ^ 4).trans hd)
      have g1171 := S1 1171 (by norm_num) (by norm_num) (by decide) 353641 g353641 (by norm_num)
      have g293 := S1 293 (by norm_num) (by norm_num) (by decide) 1171 g1171 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 293 g293 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 31
    · simp
    · exfalso; have hd := D2 he
      have g13 := S7 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 31 ^ 2).trans hd)
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 31 ^ 2).trans hd)
      have g7 := S1 7 (by norm_num) (by norm_num) (by decide) 13 g13 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      have g3 := S1 3 (by norm_num) (by norm_num) (by decide) 5 g5 (by norm_num)
      exact WK [13, 37, 7, 19, 5, 3] (by decide)
        (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (by norm_num)
    · exfalso; have hd := D4 he
      have g409 := S7 409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 409 ∣ 1 + 31 ^ 4).trans hd)
      have g1129 := S7 1129 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1129 ∣ 1 + 31 ^ 4).trans hd)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 409 g409 1129 g1129 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 37
    · simp
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 37 ^ 2).trans hd)
      have g137 := S7 137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 137 ∣ 1 + 37 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 137 g137 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g10529 := S7 10529 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10529 ∣ 1 + 37 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 10529 g10529 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 41
    · simp
    · exfalso; have hd := D2 he
      exact SQ 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 * 29 ∣ 1 + 41 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g10313 := S7 10313 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10313 ∣ 1 + 41 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 10313 g10313 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 43
    · simp
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 43 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 43 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 47
    · simp
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 47 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 47 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 53
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 53 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 53 ^ 2).trans hd)
      have g281 := S7 281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 281 ∣ 1 + 53 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 281 g281 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 53 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 59
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 59 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 59 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g1741 := S7 1741 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1741 ∣ 1 + 59 ^ 2).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 1741 g1741 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 59 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 61
    · simp
    · exfalso; have hd := D2 he
      have g1861 := S7 1861 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1861 ∣ 1 + 61 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 1861 g1861 (by norm_num)
    · exfalso; have hd := D4 he
      have g6922921 := S7 6922921 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6922921 ∣ 1 + 61 ^ 4).trans hd)
      have g93553 := S1 93553 (by norm_num) (by norm_num) (by decide) 6922921 g6922921 (by norm_num)
      have g1613 := S1 1613 (by norm_num) (by norm_num) (by decide) 93553 g93553 (by norm_num)
      have g269 := S1 269 (by norm_num) (by norm_num) (by decide) 1613 g1613 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 269 g269 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 67
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 67 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 67 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
    · exfalso; have hd := D4 he
      have g10753 := S7 10753 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10753 ∣ 1 + 67 ^ 4).trans hd)
      have g283 := S1 283 (by norm_num) (by norm_num) (by decide) 10753 g10753 (by norm_num)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 283 g283 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 71
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 71 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g2521 := S7 2521 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2521 ∣ 1 + 71 ^ 2).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 2521 g2521 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D4 he
      have g12705841 := S7 12705841 (by norm_num) (by norm_num) (by decide) ((by norm_num : 12705841 ∣ 1 + 71 ^ 4).trans hd)
      have g50023 := S1 50023 (by norm_num) (by norm_num) (by decide) 12705841 g12705841 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 50023 g50023 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 73
    · simp
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 73 ^ 2).trans hd)
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 73 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g14199121 := S7 14199121 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14199121 ∣ 1 + 73 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 14199121 g14199121 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 79
    · simp
    · exfalso; have hd := D2 he
      have g3121 := S7 3121 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3121 ∣ 1 + 79 ^ 2).trans hd)
      have g223 := S1 223 (by norm_num) (by norm_num) (by decide) 3121 g3121 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 3121 g3121 223 g223 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1097 := S7 1097 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1097 ∣ 1 + 79 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1097 g1097 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 83
    · simp
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 83 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 83 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 89
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 89 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 89 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g111641 := S7 111641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 111641 ∣ 1 + 89 ^ 4).trans hd)
      have g809 := S1 809 (by norm_num) (by norm_num) (by decide) 111641 g111641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 809 g809 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 97
    · exfalso; have hd := D1 he
      exact SQ 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 * 7 ∣ 1 + 97 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 97 ^ 2).trans hd)
      have g941 := S7 941 (by norm_num) (by norm_num) (by decide) ((by norm_num : 941 ∣ 1 + 97 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 941 g941 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g233 := S7 233 (by norm_num) (by norm_num) (by decide) ((by norm_num : 233 ∣ 1 + 97 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 233 g233 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 101
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 101 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g5101 := S7 5101 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5101 ∣ 1 + 101 ^ 2).trans hd)
      have g2551 := S1 2551 (by norm_num) (by norm_num) (by decide) 5101 g5101 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 2551 g2551 (by norm_num)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 2551 g2551 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 29 g29 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 101 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 103
    · simp
    · exfalso; have hd := D2 he
      have g1061 := S7 1061 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1061 ∣ 1 + 103 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1061 g1061 (by norm_num)
    · exfalso; have hd := D4 he
      have g56275441 := S7 56275441 prime_56275441 (by norm_num) (by decide) ((by norm_num : 56275441 ∣ 1 + 103 ^ 4).trans hd)
      have g28137721 := S1 28137721 (by norm_num) (by norm_num) (by decide) 56275441 g56275441 (by norm_num)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 28137721 g28137721 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 107
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 107 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 107 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g15601 := S7 15601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15601 ∣ 1 + 107 ^ 4).trans hd)
      have g269 := S1 269 (by norm_num) (by norm_num) (by decide) 15601 g15601 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 269 g269 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 109
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 109 ^ 1).trans hd)
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 109 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g457 := S7 457 (by norm_num) (by norm_num) (by decide) ((by norm_num : 457 ∣ 1 + 109 ^ 2).trans hd)
      have g229 := S1 229 (by norm_num) (by norm_num) (by decide) 457 g457 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 229 g229 (by norm_num)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 229 g229 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 109 ^ 4).trans hd)
      have g1721441 := S7 1721441 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1721441 ∣ 1 + 109 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 41 g41 1721441 g1721441 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 113
    · exfalso; have hd := D1 he
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 113 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 113 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g1277 := S7 1277 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1277 ∣ 1 + 113 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1277 g1277 (by norm_num)
    · exfalso; have hd := D4 he
      have g81523681 := S7 81523681 prime_81523681 (by norm_num) (by decide) ((by norm_num : 81523681 ∣ 1 + 113 ^ 4).trans hd)
      have g4621 := S1 4621 (by norm_num) (by norm_num) (by decide) 81523681 g81523681 (by norm_num)
      have g2311 := S1 2311 (by norm_num) (by norm_num) (by decide) 4621 g4621 (by norm_num)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 2311 g2311 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 127
    · simp
    · exfalso; have hd := D2 he
      have g1613 := S7 1613 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1613 ∣ 1 + 127 ^ 2).trans hd)
      have g269 := S1 269 (by norm_num) (by norm_num) (by decide) 1613 g1613 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 269 g269 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 127 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 131
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 131 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 131 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g8581 := S7 8581 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8581 ∣ 1 + 131 ^ 2).trans hd)
      have g613 := S1 613 (by norm_num) (by norm_num) (by decide) 8581 g8581 (by norm_num)
      have g307 := S1 307 (by norm_num) (by norm_num) (by decide) 613 g613 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 8581 g8581 307 g307 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1303097 := S7 1303097 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1303097 ∣ 1 + 131 ^ 4).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 1303097 g1303097 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 137
    · exfalso; have hd := D1 he
      have g23 := S7 23 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23 ∣ 1 + 137 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 137 ^ 1).trans hd) 23 g23 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 137 ^ 2).trans hd)
      have g1877 := S7 1877 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1877 ∣ 1 + 137 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 1877 g1877 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g3049 := S7 3049 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3049 ∣ 1 + 137 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 3049 g3049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 139
    · simp
    · simp
    · exfalso; have hd := D4 he
      have g617 := S7 617 (by norm_num) (by norm_num) (by decide) ((by norm_num : 617 ∣ 1 + 139 ^ 4).trans hd)
      have g302513 := S7 302513 (by norm_num) (by norm_num) (by decide) ((by norm_num : 302513 ∣ 1 + 139 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 617 g617 302513 g302513 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 149
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 149 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 149 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g7001 := S7 7001 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7001 ∣ 1 + 149 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 7001 g7001 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 151
    · simp
    · exfalso; have hd := D2 he
      have g877 := S7 877 (by norm_num) (by norm_num) (by decide) ((by norm_num : 877 ∣ 1 + 151 ^ 2).trans hd)
      have g439 := S1 439 (by norm_num) (by norm_num) (by decide) 877 g877 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 439 g439 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 439 g439 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 151 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 157
    · simp
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 157 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g2688377 := S7 2688377 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2688377 ∣ 1 + 157 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 2688377 g2688377 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 163
    · simp
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 163 ^ 2).trans hd)
      have g2657 := S7 2657 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2657 ∣ 1 + 163 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 2657 g2657 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g587281 := S7 587281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 587281 ∣ 1 + 163 ^ 4).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 587281 g587281 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 167
    · simp
    · exfalso; have hd := D2 he
      have g2789 := S7 2789 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2789 ∣ 1 + 167 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2789 g2789 (by norm_num)
    · exfalso; have hd := D4 he
      have g9485321 := S7 9485321 (by norm_num) (by norm_num) (by decide) ((by norm_num : 9485321 ∣ 1 + 167 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 9485321 g9485321 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 173
    · exfalso; have hd := D1 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 173 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 173 ^ 1).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 173 ^ 2).trans hd)
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 173 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g769 := S7 769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 769 ∣ 1 + 173 ^ 4).trans hd)
      have g582409 := S7 582409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 582409 ∣ 1 + 173 ^ 4).trans hd)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 769 g769 582409 g582409 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 179
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 179 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 179 ^ 2).trans hd)
      have g433 := S7 433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 433 ∣ 1 + 179 ^ 2).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g7 := S1 7 (by norm_num) (by norm_num) (by decide) 433 g433 (by norm_num)
      have g31 := S1 31 (by norm_num) (by norm_num) (by decide) 433 g433 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      have g3 := S1 3 (by norm_num) (by norm_num) (by decide) 5 g5 (by norm_num)
      exact WK [37, 433, 19, 7, 31, 5, 3] (by decide)
        (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (by norm_num)
    · exfalso; have hd := D4 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 179 ^ 4).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 181
    · exfalso; have hd := D1 he
      have g13 := S7 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 181 ^ 1).trans hd)
      exact S8 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 ∣ 1 + 181 ^ 1).trans hd) 13 g13 (by norm_num)
    · simp
    · exfalso; have hd := D4 he
      have g301993 := S7 301993 (by norm_num) (by norm_num) (by decide) ((by norm_num : 301993 ∣ 1 + 181 ^ 4).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 301993 g301993 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 191
    · simp
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 191 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g16230041 := S7 16230041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 16230041 ∣ 1 + 191 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 16230041 g16230041 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 193
    · exfalso; have hd := D1 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 193 ^ 1).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 193 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 193 ^ 4).trans hd)
      have g2699393 := S7 2699393 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2699393 ∣ 1 + 193 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 2699393 g2699393 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 197
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 197 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g3881 := S7 3881 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3881 ∣ 1 + 197 ^ 2).trans hd)
      have g647 := S1 647 (by norm_num) (by norm_num) (by decide) 3881 g3881 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 647 g647 (by norm_num)
    · exfalso; have hd := D4 he
      have g73 := S7 73 (by norm_num) (by norm_num) (by decide) ((by norm_num : 73 ∣ 1 + 197 ^ 4).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 73 g73 (by norm_num)
      have g10316017 := S7 10316017 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10316017 ∣ 1 + 197 ^ 4).trans hd)
      have g151 := S1 151 (by norm_num) (by norm_num) (by decide) 10316017 g10316017 (by norm_num)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 37 g37 151 g151 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 199
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 199 ^ 1).trans hd)
    · simp
    · exfalso; have hd := D4 he
      have g784119601 := S7 784119601 prime_784119601 (by norm_num) (by decide) ((by norm_num : 784119601 ∣ 1 + 199 ^ 4).trans hd)
      have g56008543 := S1 56008543 prime_56008543 (by norm_num) (by decide) 784119601 g784119601 (by norm_num)
      have g1750267 := S1 1750267 (by norm_num) (by norm_num) (by decide) 56008543 g56008543 (by norm_num)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 1750267 g1750267 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 211
    · exfalso; have hd := D1 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 211 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D2 he
      have g197 := S7 197 (by norm_num) (by norm_num) (by decide) ((by norm_num : 197 ∣ 1 + 211 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
    · exfalso; have hd := D4 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 211 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 223
    · simp
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 223 ^ 2).trans hd)
      have g4973 := S7 4973 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4973 ∣ 1 + 223 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 4973 g4973 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 223 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 227
    · exfalso; have hd := D1 he
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 227 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 227 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 227 ^ 2).trans hd)
      have g5153 := S7 5153 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5153 ∣ 1 + 227 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 5153 g5153 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 227 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 229
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 229 ^ 1).trans hd)
      have g23 := S7 23 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23 ∣ 1 + 229 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g2017 := S7 2017 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2017 ∣ 1 + 229 ^ 2).trans hd)
      have g1009 := S1 1009 (by norm_num) (by norm_num) (by decide) 2017 g2017 (by norm_num)
      have g101 := S1 101 (by norm_num) (by norm_num) (by decide) 1009 g1009 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 101 g101 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 229 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 233
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 233 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 233 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
    · exfalso; have hd := D4 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 233 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 239
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 239 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 239 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 * 13 ∣ 1 + 239 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g809 := S7 809 (by norm_num) (by norm_num) (by decide) ((by norm_num : 809 ∣ 1 + 239 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 809 g809 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 241
    · exfalso; have hd := D1 he
      exact SQ 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 * 11 ∣ 1 + 241 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 241 ^ 2).trans hd)
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 241 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 257 g257 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 241 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 251
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 251 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 251 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g1984563001 := S7 1984563001 prime_1984563001 (by norm_num) (by decide) ((by norm_num : 1984563001 ∣ 1 + 251 ^ 4).trans hd)
      have g747763 := S1 747763 (by norm_num) (by norm_num) (by decide) 1984563001 g1984563001 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 747763 g747763 (by norm_num)
      have g9839 := S1 9839 (by norm_num) (by norm_num) (by decide) 747763 g747763 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 19 g19 9839 g9839 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 257
    · exfalso; have hd := D1 he
      have g43 := S7 43 (by norm_num) (by norm_num) (by decide) ((by norm_num : 43 ∣ 1 + 257 ^ 1).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 257 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 257 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 257 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 263
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 263 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 263 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 263 ^ 2).trans hd)
      have g6917 := S7 6917 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6917 ∣ 1 + 263 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 6917 g6917 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g3041 := S7 3041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3041 ∣ 1 + 263 ^ 4).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 3041 g3041 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 269
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 269 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 269 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D4 he
      have g85577 := S7 85577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 85577 ∣ 1 + 269 ^ 4).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 85577 g85577 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 271
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 271 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
    · exfalso; have hd := D4 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 271 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 277
    · simp
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 277 ^ 2).trans hd)
      have g7673 := S7 7673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7673 ∣ 1 + 277 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 7673 g7673 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g569 := S7 569 (by norm_num) (by norm_num) (by decide) ((by norm_num : 569 ∣ 1 + 277 ^ 4).trans hd)
      have g5173409 := S7 5173409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5173409 ∣ 1 + 277 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 569 g569 5173409 g5173409 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 281
    · exfalso; have hd := D1 he
      have g47 := S7 47 (by norm_num) (by norm_num) (by decide) ((by norm_num : 47 ∣ 1 + 281 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 281 ^ 1).trans hd) 47 g47 (by norm_num)
    · exfalso; have hd := D2 he
      have g3037 := S7 3037 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3037 ∣ 1 + 281 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 3037 g3037 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 281 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 283
    · exfalso; have hd := D1 he
      have g71 := S7 71 (by norm_num) (by norm_num) (by decide) ((by norm_num : 71 ∣ 1 + 283 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
    · exfalso; have hd := D2 he
      have g8009 := S7 8009 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8009 ∣ 1 + 283 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 8009 g8009 (by norm_num)
    · exfalso; have hd := D4 he
      have g9085337 := S7 9085337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 9085337 ∣ 1 + 283 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 9085337 g9085337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 293
    · exfalso; have hd := D1 he
      exact SQ 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 * 7 ∣ 1 + 293 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 293 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g25673 := S7 25673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 25673 ∣ 1 + 293 ^ 4).trans hd)
      have g143537 := S7 143537 (by norm_num) (by norm_num) (by decide) ((by norm_num : 143537 ∣ 1 + 293 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 25673 g25673 143537 g143537 (by norm_num) (by norm_num)) (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_300 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 300 ≤ z) (hi : z < 600)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 2 = 1 → z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ)) ∧
    (e % 4 = 2 → z ∈ ({11, 139, 181, 199, 271} : Finset ℕ)) ∧
    (e % 8 = 4 → z ∈ ({7, 11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D1 : e % 2 = 1 → 1 + z ^ 1 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D2 : e % 4 = 2 → 1 + z ^ 2 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D4 : e % 8 = 4 → 1 + z ^ 4 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have WK : ∀ L : List ℕ, L.Nodup → (∀ x ∈ L, x ∈ P) →
      2 * L.prod ≤ (L.map (fun p => p + 1)).prod → False := fun L h1 h2 h3 => weight_kill hP E h1 h2 h3
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 307
    · simp
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 307 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g33937 := S7 33937 (by norm_num) (by norm_num) (by decide) ((by norm_num : 33937 ∣ 1 + 307 ^ 4).trans hd)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 33937 g33937 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 311
    · simp
    · exfalso; have hd := D2 he
      have g137 := S7 137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 137 ∣ 1 + 311 ^ 2).trans hd)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 137 g137 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 137 g137 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g2897 := S7 2897 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2897 ∣ 1 + 311 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2897 g2897 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 313
    · simp
    · exfalso; have hd := D2 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 313 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D4 he
      have g4798962481 := S7 4798962481 prime_4798962481 (by norm_num) (by decide) ((by norm_num : 4798962481 ∣ 1 + 313 ^ 4).trans hd)
      have g268729 := S1 268729 (by norm_num) (by norm_num) (by decide) 4798962481 g4798962481 (by norm_num)
      have g349 := S1 349 (by norm_num) (by norm_num) (by decide) 268729 g268729 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 349 g349 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 317
    · exfalso; have hd := D1 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 317 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D2 he
      have g773 := S7 773 (by norm_num) (by norm_num) (by decide) ((by norm_num : 773 ∣ 1 + 317 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 773 g773 (by norm_num)
    · exfalso; have hd := D4 he
      have g5049019561 := S7 5049019561 prime_5049019561 (by norm_num) (by decide) ((by norm_num : 5049019561 ∣ 1 + 317 ^ 4).trans hd)
      have g1789 := S1 1789 (by norm_num) (by norm_num) (by decide) 5049019561 g5049019561 (by norm_num)
      have g179 := S1 179 (by norm_num) (by norm_num) (by decide) 1789 g1789 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 179 g179 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 331
    · simp
    · exfalso; have hd := D2 he
      have g1889 := S7 1889 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1889 ∣ 1 + 331 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1889 g1889 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 331 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 337
    · exfalso; have hd := D1 he
      exact SQ 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 * 13 ∣ 1 + 337 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 337 ^ 2).trans hd)
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 337 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g6448958881 := S7 6448958881 prime_6448958881 (by norm_num) (by decide) ((by norm_num : 6448958881 ∣ 1 + 337 ^ 4).trans hd)
      have g233641 := S1 233641 (by norm_num) (by norm_num) (by decide) 6448958881 g6448958881 (by norm_num)
      have g197 := S1 197 (by norm_num) (by norm_num) (by decide) 233641 g233641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 347
    · exfalso; have hd := D1 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 347 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 347 ^ 1).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D2 he
      have g12041 := S7 12041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 12041 ∣ 1 + 347 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 12041 g12041 (by norm_num)
    · exfalso; have hd := D4 he
      have g673 := S7 673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 673 ∣ 1 + 347 ^ 4).trans hd)
      have g337 := S1 337 (by norm_num) (by norm_num) (by decide) 673 g673 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 349
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 349 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g60901 := S7 60901 (by norm_num) (by norm_num) (by decide) ((by norm_num : 60901 ∣ 1 + 349 ^ 2).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 60901 g60901 (by norm_num)
      have g823 := S1 823 (by norm_num) (by norm_num) (by decide) 60901 g60901 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g103 := S1 103 (by norm_num) (by norm_num) (by decide) 823 g823 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 103 g103 (by norm_num)
      have g3 := S1 3 (by norm_num) (by norm_num) (by decide) 5 g5 (by norm_num)
      have g7 := S1 7 (by norm_num) (by norm_num) (by decide) 13 g13 (by norm_num)
      exact WK [60901, 37, 823, 19, 103, 5, 13, 3, 7] (by decide)
        (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 349 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 353
    · exfalso; have hd := D1 he
      have g59 := S7 59 (by norm_num) (by norm_num) (by decide) ((by norm_num : 59 ∣ 1 + 353 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 353 ^ 1).trans hd) 59 g59 (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 353 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g7763701441 := S7 7763701441 prime_7763701441 (by norm_num) (by decide) ((by norm_num : 7763701441 ∣ 1 + 353 ^ 4).trans hd)
      have g283 := S1 283 (by norm_num) (by norm_num) (by decide) 7763701441 g7763701441 (by norm_num)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 283 g283 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 359
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 359 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g4957 := S7 4957 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4957 ∣ 1 + 359 ^ 2).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 4957 g4957 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 359 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 367
    · simp
    · exfalso; have hd := D2 he
      have g13469 := S7 13469 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13469 ∣ 1 + 367 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 367 ^ 2).trans hd) 13469 g13469 (by norm_num)
    · exfalso; have hd := D4 he
      have g232049 := S7 232049 (by norm_num) (by norm_num) (by decide) ((by norm_num : 232049 ∣ 1 + 367 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 232049 g232049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 373
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 373 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g13913 := S7 13913 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13913 ∣ 1 + 373 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 13913 g13913 (by norm_num)
    · exfalso; have hd := D4 he
      have g178513 := S7 178513 (by norm_num) (by norm_num) (by decide) ((by norm_num : 178513 ∣ 1 + 373 ^ 4).trans hd)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 178513 g178513 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 178513 g178513 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 379
    · exfalso; have hd := D1 he
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 379 ^ 1).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 379 ^ 1).trans hd) 19 g19 (by norm_num)
    · exfalso; have hd := D2 he
      have g71821 := S7 71821 (by norm_num) (by norm_num) (by decide) ((by norm_num : 71821 ∣ 1 + 379 ^ 2).trans hd)
      have g35911 := S1 35911 (by norm_num) (by norm_num) (by decide) 71821 g71821 (by norm_num)
      exact S6 67 (by norm_num) (by norm_num) (by decide) 35911 g35911 (by norm_num)
    · exfalso; have hd := D4 he
      have g3882713 := S7 3882713 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3882713 ∣ 1 + 379 ^ 4).trans hd)
      have g89 := S1 89 (by norm_num) (by norm_num) (by decide) 3882713 g3882713 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 383
    · simp
    · exfalso; have hd := D2 he
      have g14669 := S7 14669 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14669 ∣ 1 + 383 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 14669 g14669 (by norm_num)
    · exfalso; have hd := D4 he
      have g136601 := S7 136601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 136601 ∣ 1 + 383 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 136601 g136601 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 389
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 389 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 389 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g2609 := S7 2609 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2609 ∣ 1 + 389 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2609 g2609 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 389 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 397
    · exfalso; have hd := D1 he
      have g199 := S7 199 (by norm_num) (by norm_num) (by decide) ((by norm_num : 199 ∣ 1 + 397 ^ 1).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 199 g199 (by norm_num)
    · exfalso; have hd := D2 he
      have g15761 := S7 15761 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15761 ∣ 1 + 397 ^ 2).trans hd)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 15761 g15761 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
    · exfalso; have hd := D4 he
      have g8341369 := S7 8341369 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8341369 ∣ 1 + 397 ^ 4).trans hd)
      have g834137 := S1 834137 (by norm_num) (by norm_num) (by decide) 8341369 g8341369 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 834137 g834137 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 401
    · exfalso; have hd := D1 he
      have g67 := S7 67 (by norm_num) (by norm_num) (by decide) ((by norm_num : 67 ∣ 1 + 401 ^ 1).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 401 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g137 := S7 137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 137 ∣ 1 + 401 ^ 4).trans hd)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 137 g137 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 137 g137 23 g23 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 409
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 409 ^ 1).trans hd)
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 409 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g83641 := S7 83641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 83641 ∣ 1 + 409 ^ 2).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 83641 g83641 (by norm_num)
      have g3217 := S1 3217 (by norm_num) (by norm_num) (by decide) 83641 g83641 (by norm_num)
      have g1609 := S1 1609 (by norm_num) (by norm_num) (by decide) 3217 g3217 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 13 g13 1609 g1609 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g3712249 := S7 3712249 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3712249 ∣ 1 + 409 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 3712249 g3712249 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 419
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 419 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 419 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g2141 := S7 2141 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2141 ∣ 1 + 419 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2141 g2141 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 421
    · exfalso; have hd := D1 he
      have g211 := S7 211 (by norm_num) (by norm_num) (by decide) ((by norm_num : 211 ∣ 1 + 421 ^ 1).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 211 g211 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 421 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g1181969 := S7 1181969 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1181969 ∣ 1 + 421 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1181969 g1181969 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 431
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 431 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g293 := S7 293 (by norm_num) (by norm_num) (by decide) ((by norm_num : 293 ∣ 1 + 431 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 293 g293 (by norm_num)
    · exfalso; have hd := D4 he
      have g17253574561 := S7 17253574561 prime_17253574561 (by norm_num) (by decide) ((by norm_num : 17253574561 ∣ 1 + 431 ^ 4).trans hd)
      have g421621 := S1 421621 (by norm_num) (by norm_num) (by decide) 17253574561 g17253574561 (by norm_num)
      have g210811 := S1 210811 (by norm_num) (by norm_num) (by decide) 421621 g421621 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 17253574561 g17253574561 210811 g210811 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 433
    · simp
    · exfalso; have hd := D2 he
      have g18749 := S7 18749 (by norm_num) (by norm_num) (by decide) ((by norm_num : 18749 ∣ 1 + 433 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 18749 g18749 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 433 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 439
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 439 ^ 1).trans hd)
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 439 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g557 := S7 557 (by norm_num) (by norm_num) (by decide) ((by norm_num : 557 ∣ 1 + 439 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 557 g557 (by norm_num)
    · exfalso; have hd := D4 he
      have g19007873 := S7 19007873 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19007873 ∣ 1 + 439 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 19007873 g19007873 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 443
    · exfalso; have hd := D1 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 443 ^ 1).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 443 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 443 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g235849 := S7 235849 (by norm_num) (by norm_num) (by decide) ((by norm_num : 235849 ∣ 1 + 443 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 235849 g235849 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 449
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 449 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g100801 := S7 100801 (by norm_num) (by norm_num) (by decide) ((by norm_num : 100801 ∣ 1 + 449 ^ 2).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 100801 g100801 (by norm_num)
      have g3877 := S1 3877 (by norm_num) (by norm_num) (by decide) 100801 g100801 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 13 g13 3877 g3877 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g20321481601 := S7 20321481601 prime_20321481601 (by norm_num) (by decide) ((by norm_num : 20321481601 ∣ 1 + 449 ^ 4).trans hd)
      have g199 := S1 199 (by norm_num) (by norm_num) (by decide) 20321481601 g20321481601 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 199 g199 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 457
    · exfalso; have hd := D1 he
      have g229 := S7 229 (by norm_num) (by norm_num) (by decide) ((by norm_num : 229 ∣ 1 + 457 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 229 g229 (by norm_num)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 229 g229 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 457 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 457 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 461
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 461 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 461 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g106261 := S7 106261 (by norm_num) (by norm_num) (by decide) ((by norm_num : 106261 ∣ 1 + 461 ^ 2).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 106261 g106261 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 461 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 463
    · exfalso; have hd := D1 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 463 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 29 g29 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29 g29 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 463 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 467
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 467 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 467 ^ 2).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 467 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 479
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 479 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 479 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 479 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
    · exfalso; have hd := D4 he
      have g26321586241 := S7 26321586241 prime_26321586241 (by norm_num) (by decide) ((by norm_num : 26321586241 ∣ 1 + 479 ^ 4).trans hd)
      have g1021 := S1 1021 (by norm_num) (by norm_num) (by decide) 26321586241 g26321586241 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 26321586241 g26321586241 1021 g1021 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 487
    · simp
    · exfalso; have hd := D2 he
      have g641 := S7 641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 641 ∣ 1 + 487 ^ 2).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 641 g641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
    · exfalso; have hd := D4 he
      have g28124567281 := S7 28124567281 prime_28124567281 (by norm_num) (by decide) ((by norm_num : 28124567281 ∣ 1 + 487 ^ 4).trans hd)
      have g3183673 := S1 3183673 (by norm_num) (by norm_num) (by decide) 28124567281 g28124567281 (by norm_num)
      have g122449 := S1 122449 (by norm_num) (by norm_num) (by decide) 3183673 g3183673 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 122449 g122449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 491
    · exfalso; have hd := D1 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 491 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 491 ^ 1).trans hd) 41 g41 (by norm_num)
    · exfalso; have hd := D2 he
      have g809 := S7 809 (by norm_num) (by norm_num) (by decide) ((by norm_num : 809 ∣ 1 + 491 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 809 g809 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 491 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 499
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 499 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g13 := S7 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 499 ^ 2).trans hd)
      have g157 := S7 157 (by norm_num) (by norm_num) (by decide) ((by norm_num : 157 ∣ 1 + 499 ^ 2).trans hd)
      have g7 := S1 7 (by norm_num) (by norm_num) (by decide) 13 g13 (by norm_num)
      have g79 := S1 79 (by norm_num) (by norm_num) (by decide) 157 g157 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 79 g79 (by norm_num)
      have g3 := S1 3 (by norm_num) (by norm_num) (by decide) 5 g5 (by norm_num)
      exact WK [13, 157, 7, 79, 5, 3] (by decide)
        (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (by norm_num)
    · exfalso; have hd := D4 he
      have g10457 := S7 10457 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10457 ∣ 1 + 499 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 10457 g10457 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 503
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 503 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 503 ^ 2).trans hd)
      have g25301 := S7 25301 (by norm_num) (by norm_num) (by decide) ((by norm_num : 25301 ∣ 1 + 503 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 25301 g25301 (by norm_num) (by norm_num)) (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 509
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 509 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g281 := S7 281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 281 ∣ 1 + 509 ^ 2).trans hd)
      have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 281 g281 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 281 g281 47 g47 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g6353 := S7 6353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6353 ∣ 1 + 509 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 6353 g6353 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 521
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 521 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g135721 := S7 135721 (by norm_num) (by norm_num) (by decide) ((by norm_num : 135721 ∣ 1 + 521 ^ 2).trans hd)
      have g79 := S1 79 (by norm_num) (by norm_num) (by decide) 135721 g135721 (by norm_num)
      have g859 := S1 859 (by norm_num) (by norm_num) (by decide) 135721 g135721 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 79 g79 859 g859 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 521 ^ 4).trans hd)
      have g4466009 := S7 4466009 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4466009 ∣ 1 + 521 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 4466009 g4466009 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 523
    · exfalso; have hd := D1 he
      have g131 := S7 131 (by norm_num) (by norm_num) (by decide) ((by norm_num : 131 ∣ 1 + 523 ^ 1).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 131 g131 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 131 g131 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 523 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g37409056921 := S7 37409056921 prime_37409056921 (by norm_num) (by decide) ((by norm_num : 37409056921 ∣ 1 + 523 ^ 4).trans hd)
      have g30513097 := S1 30513097 (by norm_num) (by norm_num) (by decide) 37409056921 g37409056921 (by norm_num)
      have g571 := S1 571 (by norm_num) (by norm_num) (by decide) 30513097 g30513097 (by norm_num)
      exact absurd (S3 11 (by norm_num) (by norm_num) (by decide) 30513097 g30513097 571 g571 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 541
    · exfalso; have hd := D1 he
      have g271 := S7 271 (by norm_num) (by norm_num) (by decide) ((by norm_num : 271 ∣ 1 + 541 ^ 1).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 271 g271 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g11257 := S7 11257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11257 ∣ 1 + 541 ^ 2).trans hd)
      exact S8 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 541 ^ 2).trans hd) 11257 g11257 (by norm_num)
    · exfalso; have hd := D4 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 541 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 547
    · exfalso; have hd := D1 he
      have g137 := S7 137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 137 ∣ 1 + 547 ^ 1).trans hd)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 137 g137 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 137 g137 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 547 ^ 2).trans hd)
      have g29921 := S7 29921 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29921 ∣ 1 + 547 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 29921 g29921 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 547 ^ 4).trans hd)
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 547 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 41 g41 113 g113 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 557
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 557 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 557 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g1875793 := S7 1875793 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1875793 ∣ 1 + 557 ^ 4).trans hd)
      have g49363 := S1 49363 (by norm_num) (by norm_num) (by decide) 1875793 g1875793 (by norm_num)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 49363 g49363 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 49363 g49363 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 563
    · exfalso; have hd := D1 he
      have g47 := S7 47 (by norm_num) (by norm_num) (by decide) ((by norm_num : 47 ∣ 1 + 563 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 563 ^ 1).trans hd) 47 g47 (by norm_num)
    · exfalso; have hd := D2 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 563 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 563 ^ 2).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D4 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 563 ^ 4).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 569
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 569 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 569 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g161881 := S7 161881 (by norm_num) (by norm_num) (by decide) ((by norm_num : 161881 ∣ 1 + 569 ^ 2).trans hd)
      have g373 := S1 373 (by norm_num) (by norm_num) (by decide) 161881 g161881 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 373 g373 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 569 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 571
    · simp
    · exfalso; have hd := D2 he
      have g163021 := S7 163021 (by norm_num) (by norm_num) (by decide) ((by norm_num : 163021 ∣ 1 + 571 ^ 2).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 163021 g163021 (by norm_num)
      have g2203 := S1 2203 (by norm_num) (by norm_num) (by decide) 163021 g163021 (by norm_num)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 37 g37 2203 g2203 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 571 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 577
    · exfalso; have hd := D1 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 577 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 * 13 ∣ 1 + 577 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g1351728281 := S7 1351728281 prime_1351728281 (by norm_num) (by decide) ((by norm_num : 1351728281 ∣ 1 + 577 ^ 4).trans hd)
      have g113381 := S1 113381 (by norm_num) (by norm_num) (by decide) 1351728281 g1351728281 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 113381 g113381 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 587
    · exfalso; have hd := D1 he
      exact SQ 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 * 7 ∣ 1 + 587 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 587 ^ 2).trans hd)
      have g34457 := S7 34457 (by norm_num) (by norm_num) (by decide) ((by norm_num : 34457 ∣ 1 + 587 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 34457 g34457 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g77681 := S7 77681 (by norm_num) (by norm_num) (by decide) ((by norm_num : 77681 ∣ 1 + 587 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 77681 g77681 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 593
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 593 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 593 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 593 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 599
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 599 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 599 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g4153 := S7 4153 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4153 ∣ 1 + 599 ^ 4).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 4153 g4153 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_600 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 600 ≤ z) (hi : z < 900)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 2 = 1 → z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ)) ∧
    (e % 4 = 2 → z ∈ ({11, 139, 181, 199, 271} : Finset ℕ)) ∧
    (e % 8 = 4 → z ∈ ({7, 11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D1 : e % 2 = 1 → 1 + z ^ 1 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D2 : e % 4 = 2 → 1 + z ^ 2 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D4 : e % 8 = 4 → 1 + z ^ 4 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have WK : ∀ L : List ℕ, L.Nodup → (∀ x ∈ L, x ∈ P) →
      2 * L.prod ≤ (L.map (fun p => p + 1)).prod → False := fun L h1 h2 h3 => weight_kill hP E h1 h2 h3
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 601
    · simp
    · exfalso; have hd := D2 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 601 ^ 2).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
    · exfalso; have hd := D4 he
      have g1591050761 := S7 1591050761 prime_1591050761 (by norm_num) (by decide) ((by norm_num : 1591050761 ∣ 1 + 601 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1591050761 g1591050761 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 607
    · simp
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 607 ^ 2).trans hd)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 613
    · simp
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 613 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g70601170681 := S7 70601170681 prime_70601170681 (by norm_num) (by decide) ((by norm_num : 70601170681 ∣ 1 + 613 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 70601170681 g70601170681 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 617
    · simp
    · exfalso; have hd := D2 he
      have g38069 := S7 38069 (by norm_num) (by norm_num) (by decide) ((by norm_num : 38069 ∣ 1 + 617 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 38069 g38069 (by norm_num)
    · exfalso; have hd := D4 he
      have g953 := S7 953 (by norm_num) (by norm_num) (by decide) ((by norm_num : 953 ∣ 1 + 617 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 953 g953 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 619
    · simp
    · exfalso; have hd := D2 he
      have g14737 := S7 14737 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14737 ∣ 1 + 619 ^ 2).trans hd)
      have g7369 := S1 7369 (by norm_num) (by norm_num) (by decide) 14737 g14737 (by norm_num)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 7369 g7369 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g26113 := S7 26113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 26113 ∣ 1 + 619 ^ 4).trans hd)
      have g1187 := S1 1187 (by norm_num) (by norm_num) (by decide) 26113 g26113 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1187 g1187 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 631
    · simp
    · exfalso; have hd := D2 he
      have g199081 := S7 199081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 199081 ∣ 1 + 631 ^ 2).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 199081 g199081 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 631 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 641
    · exfalso; have hd := D1 he
      have g107 := S7 107 (by norm_num) (by norm_num) (by decide) ((by norm_num : 107 ∣ 1 + 641 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
    · exfalso; have hd := D2 he
      have g205441 := S7 205441 (by norm_num) (by norm_num) (by decide) ((by norm_num : 205441 ∣ 1 + 641 ^ 2).trans hd)
      have g139 := S1 139 (by norm_num) (by norm_num) (by decide) 205441 g205441 (by norm_num)
      have g739 := S1 739 (by norm_num) (by norm_num) (by decide) 205441 g205441 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 139 g139 739 g739 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1034849 := S7 1034849 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1034849 ∣ 1 + 641 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1034849 g1034849 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 643
    · simp
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 643 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g85470037801 := S7 85470037801 prime_85470037801 (by norm_num) (by decide) ((by norm_num : 85470037801 ∣ 1 + 643 ^ 4).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 85470037801 g85470037801 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 647
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 647 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 647 ^ 2).trans hd)
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 647 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1200229417 := S7 1200229417 prime_1200229417 (by norm_num) (by decide) ((by norm_num : 1200229417 ∣ 1 + 647 ^ 4).trans hd)
      exact S6 31 (by norm_num) (by norm_num) (by decide) 1200229417 g1200229417 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 653
    · exfalso; have hd := D1 he
      have g109 := S7 109 (by norm_num) (by norm_num) (by decide) ((by norm_num : 109 ∣ 1 + 653 ^ 1).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 109 g109 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 653 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g42641 := S7 42641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 42641 ∣ 1 + 653 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 42641 g42641 (by norm_num)
    · exfalso; have hd := D4 he
      have g2689 := S7 2689 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2689 ∣ 1 + 653 ^ 4).trans hd)
      have g269 := S1 269 (by norm_num) (by norm_num) (by decide) 2689 g2689 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 269 g269 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 659
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 659 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 659 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 659 ^ 2).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D4 he
      have g2299999841 := S7 2299999841 prime_2299999841 (by norm_num) (by decide) ((by norm_num : 2299999841 ∣ 1 + 659 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2299999841 g2299999841 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 661
    · simp
    · exfalso; have hd := D2 he
      have g218461 := S7 218461 (by norm_num) (by norm_num) (by decide) ((by norm_num : 218461 ∣ 1 + 661 ^ 2).trans hd)
      have g5749 := S1 5749 (by norm_num) (by norm_num) (by decide) 218461 g218461 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 5749 g5749 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 661 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 673
    · exfalso; have hd := D1 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 673 ^ 1).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D2 he
      have g45293 := S7 45293 (by norm_num) (by norm_num) (by decide) ((by norm_num : 45293 ∣ 1 + 673 ^ 2).trans hd)
      have g7549 := S1 7549 (by norm_num) (by norm_num) (by decide) 45293 g45293 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 7549 g7549 (by norm_num)
    · exfalso; have hd := D4 he
      have g59417 := S7 59417 (by norm_num) (by norm_num) (by decide) ((by norm_num : 59417 ∣ 1 + 673 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 59417 g59417 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 677
    · exfalso; have hd := D1 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 677 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 677 ^ 1).trans hd) 113 g113 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 677 ^ 2).trans hd)
      have g45833 := S7 45833 (by norm_num) (by norm_num) (by decide) ((by norm_num : 45833 ∣ 1 + 677 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 45833 g45833 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g105032736121 := S7 105032736121 prime_105032736121 (by norm_num) (by decide) ((by norm_num : 105032736121 ∣ 1 + 677 ^ 4).trans hd)
      have g164299 := S1 164299 (by norm_num) (by norm_num) (by decide) 105032736121 g105032736121 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 164299 g164299 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 683
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 683 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g46649 := S7 46649 (by norm_num) (by norm_num) (by decide) ((by norm_num : 46649 ∣ 1 + 683 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 46649 g46649 (by norm_num)
    · exfalso; have hd := D4 he
      have g2653804721 := S7 2653804721 prime_2653804721 (by norm_num) (by decide) ((by norm_num : 2653804721 ∣ 1 + 683 ^ 4).trans hd)
      have g293 := S1 293 (by norm_num) (by norm_num) (by decide) 2653804721 g2653804721 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 293 g293 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 691
    · exfalso; have hd := D1 he
      have g173 := S7 173 (by norm_num) (by norm_num) (by decide) ((by norm_num : 173 ∣ 1 + 691 ^ 1).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 173 g173 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 173 g173 29 g29 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 691 ^ 2).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D4 he
      have g69497 := S7 69497 (by norm_num) (by norm_num) (by decide) ((by norm_num : 69497 ∣ 1 + 691 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 69497 g69497 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 701
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 701 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 701 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g120737471401 := S7 120737471401 prime_120737471401 (by norm_num) (by decide) ((by norm_num : 120737471401 ∣ 1 + 701 ^ 4).trans hd)
      have g102493609 := S1 102493609 prime_102493609 (by norm_num) (by decide) 120737471401 g120737471401 (by norm_num)
      have g179 := S1 179 (by norm_num) (by norm_num) (by decide) 102493609 g102493609 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 179 g179 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 709
    · exfalso; have hd := D1 he
      have g71 := S7 71 (by norm_num) (by norm_num) (by decide) ((by norm_num : 71 ∣ 1 + 709 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
    · exfalso; have hd := D2 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 709 ^ 2).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g6793 := S7 6793 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6793 ∣ 1 + 709 ^ 2).trans hd)
      have g79 := S1 79 (by norm_num) (by norm_num) (by decide) 6793 g6793 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 19 g19 79 g79 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g2377 := S7 2377 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2377 ∣ 1 + 709 ^ 4).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 2377 g2377 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 29 g29 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29 g29 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 719
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 719 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g4877 := S7 4877 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4877 ∣ 1 + 719 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 4877 g4877 (by norm_num)
    · exfalso; have hd := D4 he
      have g133624337761 := S7 133624337761 prime_133624337761 (by norm_num) (by decide) ((by norm_num : 133624337761 ∣ 1 + 719 ^ 4).trans hd)
      have g1867 := S1 1867 (by norm_num) (by norm_num) (by decide) 133624337761 g133624337761 (by norm_num)
      have g467 := S1 467 (by norm_num) (by norm_num) (by decide) 1867 g1867 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 467 g467 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 727
    · exfalso; have hd := D1 he
      have g13 := S7 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 727 ^ 1).trans hd)
      exact S8 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 ∣ 1 + 727 ^ 1).trans hd) 13 g13 (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 727 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g521 := S7 521 (by norm_num) (by norm_num) (by decide) ((by norm_num : 521 ∣ 1 + 727 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 521 g521 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 733
    · simp
    · exfalso; have hd := D2 he
      have g4133 := S7 4133 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4133 ∣ 1 + 733 ^ 2).trans hd)
      exact S8 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 733 ^ 2).trans hd) 4133 g4133 (by norm_num)
    · exfalso; have hd := D4 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 733 ^ 4).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 739
    · exfalso; have hd := D1 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 739 ^ 1).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 739 ^ 1).trans hd) 19 g19 (by norm_num)
    · exfalso; have hd := D2 he
      have g273061 := S7 273061 (by norm_num) (by norm_num) (by decide) ((by norm_num : 273061 ∣ 1 + 739 ^ 2).trans hd)
      have g136531 := S1 136531 (by norm_num) (by norm_num) (by decide) 273061 g273061 (by norm_num)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 136531 g136531 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
    · exfalso; have hd := D4 he
      have g1182689 := S7 1182689 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1182689 ∣ 1 + 739 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1182689 g1182689 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 743
    · simp
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 743 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 743 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 751
    · simp
    · exfalso; have hd := D2 he
      have g282001 := S7 282001 (by norm_num) (by norm_num) (by decide) ((by norm_num : 282001 ∣ 1 + 751 ^ 2).trans hd)
      have g20143 := S1 20143 (by norm_num) (by norm_num) (by decide) 282001 g282001 (by norm_num)
      have g1259 := S1 1259 (by norm_num) (by norm_num) (by decide) 20143 g20143 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1259 g1259 (by norm_num)
    · exfalso; have hd := D4 he
      have g508142377 := S7 508142377 prime_508142377 (by norm_num) (by decide) ((by norm_num : 508142377 ∣ 1 + 751 ^ 4).trans hd)
      have g313 := S7 313 (by norm_num) (by norm_num) (by decide) ((by norm_num : 313 ∣ 1 + 751 ^ 4).trans hd)
      have g157 := S1 157 (by norm_num) (by norm_num) (by decide) 313 g313 (by norm_num)
      exact absurd (S3 79 (by norm_num) (by norm_num) (by decide) 508142377 g508142377 157 g157 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 757
    · exfalso; have hd := D1 he
      have g379 := S7 379 (by norm_num) (by norm_num) (by decide) ((by norm_num : 379 ∣ 1 + 757 ^ 1).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 379 g379 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 379 g379 19 g19 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 757 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 757 ^ 4).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 761
    · simp
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 761 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g167690566321 := S7 167690566321 prime_167690566321 (by norm_num) (by decide) ((by norm_num : 167690566321 ∣ 1 + 761 ^ 4).trans hd)
      have g27793 := S1 27793 (by norm_num) (by norm_num) (by decide) 167690566321 g167690566321 (by norm_num)
      have g1069 := S1 1069 (by norm_num) (by norm_num) (by decide) 27793 g27793 (by norm_num)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 1069 g1069 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 769
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 769 ^ 1).trans hd)
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 769 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 769 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g174853916161 := S7 174853916161 prime_174853916161 (by norm_num) (by decide) ((by norm_num : 174853916161 ∣ 1 + 769 ^ 4).trans hd)
      have g408211 := S1 408211 (by norm_num) (by norm_num) (by decide) 174853916161 g174853916161 (by norm_num)
      exact absurd (S3 61 (by norm_num) (by norm_num) (by decide) 174853916161 g174853916161 408211 g408211 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 773
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 773 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 773 ^ 2).trans hd)
      have g59753 := S7 59753 (by norm_num) (by norm_num) (by decide) ((by norm_num : 59753 ∣ 1 + 773 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 59753 g59753 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 773 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 787
    · exfalso; have hd := D1 he
      have g197 := S7 197 (by norm_num) (by norm_num) (by decide) ((by norm_num : 197 ∣ 1 + 787 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
    · exfalso; have hd := D2 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 787 ^ 2).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D4 he
      have g409 := S7 409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 409 ∣ 1 + 787 ^ 4).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 409 g409 (by norm_num)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 409 g409 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 797
    · exfalso; have hd := D1 he
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 797 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 797 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g63521 := S7 63521 (by norm_num) (by norm_num) (by decide) ((by norm_num : 63521 ∣ 1 + 797 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 63521 g63521 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 797 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 809
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 809 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g229 := S7 229 (by norm_num) (by norm_num) (by decide) ((by norm_num : 229 ∣ 1 + 809 ^ 2).trans hd)
      have g1429 := S7 1429 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1429 ∣ 1 + 809 ^ 2).trans hd)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 229 g229 1429 g1429 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g25409 := S7 25409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 25409 ∣ 1 + 809 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 25409 g25409 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 811
    · exfalso; have hd := D1 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 811 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 29 g29 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29 g29 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g617 := S7 617 (by norm_num) (by norm_num) (by decide) ((by norm_num : 617 ∣ 1 + 811 ^ 2).trans hd)
      have g103 := S1 103 (by norm_num) (by norm_num) (by decide) 617 g617 (by norm_num)
      exact S8 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 811 ^ 2).trans hd) 103 g103 (by norm_num)
    · exfalso; have hd := D4 he
      have g216298456921 := S7 216298456921 prime_216298456921 (by norm_num) (by decide) ((by norm_num : 216298456921 ∣ 1 + 811 ^ 4).trans hd)
      have g108149228461 := S1 108149228461 prime_108149228461 (by norm_num) (by decide) 216298456921 g216298456921 (by norm_num)
      have g6545771 := S1 6545771 (by norm_num) (by norm_num) (by decide) 108149228461 g108149228461 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 6545771 g6545771 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 821
    · exfalso; have hd := D1 he
      have g137 := S7 137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 137 ∣ 1 + 821 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 821 ^ 1).trans hd) 137 g137 (by norm_num)
    · exfalso; have hd := D2 he
      have g337021 := S7 337021 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337021 ∣ 1 + 821 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 337021 g337021 (by norm_num)
    · exfalso; have hd := D4 he
      have g227165634841 := S7 227165634841 prime_227165634841 (by norm_num) (by decide) ((by norm_num : 227165634841 ∣ 1 + 821 ^ 4).trans hd)
      have g3709 := S1 3709 (by norm_num) (by norm_num) (by decide) 227165634841 g227165634841 (by norm_num)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 3709 g3709 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 823
    · simp
    · exfalso; have hd := D2 he
      have g67733 := S7 67733 (by norm_num) (by norm_num) (by decide) ((by norm_num : 67733 ∣ 1 + 823 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 67733 g67733 (by norm_num)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 823 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 827
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 827 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 827 ^ 2).trans hd)
      have g5261 := S7 5261 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5261 ∣ 1 + 827 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 5261 g5261 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g34033 := S7 34033 (by norm_num) (by norm_num) (by decide) ((by norm_num : 34033 ∣ 1 + 827 ^ 4).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 34033 g34033 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 829
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 829 ^ 1).trans hd)
      have g83 := S7 83 (by norm_num) (by norm_num) (by decide) ((by norm_num : 83 ∣ 1 + 829 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 83 g83 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 829 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g236150096041 := S7 236150096041 prime_236150096041 (by norm_num) (by decide) ((by norm_num : 236150096041 ∣ 1 + 829 ^ 4).trans hd)
      have g16867864003 := S1 16867864003 prime_16867864003 (by norm_num) (by decide) 236150096041 g236150096041 (by norm_num)
      have g221945579 := S1 221945579 prime_221945579 (by norm_num) (by decide) 16867864003 g16867864003 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 221945579 g221945579 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 839
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 839 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 839 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g3229 := S7 3229 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3229 ∣ 1 + 839 ^ 2).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 3229 g3229 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g2648257 := S7 2648257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2648257 ∣ 1 + 839 ^ 4).trans hd)
      have g69691 := S1 69691 (by norm_num) (by norm_num) (by decide) 2648257 g2648257 (by norm_num)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 2648257 g2648257 69691 g69691 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 853
    · simp
    · exfalso; have hd := D2 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 853 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 853 ^ 2).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D4 he
      have g809 := S7 809 (by norm_num) (by norm_num) (by decide) ((by norm_num : 809 ∣ 1 + 853 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 809 g809 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 857
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 857 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 857 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 857 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g269707666801 := S7 269707666801 prime_269707666801 (by norm_num) (by decide) ((by norm_num : 269707666801 ∣ 1 + 857 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 269707666801 g269707666801 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 859
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 859 ^ 1).trans hd)
      have g43 := S7 43 (by norm_num) (by norm_num) (by decide) ((by norm_num : 43 ∣ 1 + 859 ^ 1).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g2693 := S7 2693 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2693 ∣ 1 + 859 ^ 2).trans hd)
      have g449 := S1 449 (by norm_num) (by norm_num) (by decide) 2693 g2693 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 859 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 863
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 863 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 863 ^ 2).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D4 he
      have g13049 := S7 13049 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13049 ∣ 1 + 863 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 13049 g13049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 877
    · exfalso; have hd := D1 he
      have g439 := S7 439 (by norm_num) (by norm_num) (by decide) ((by norm_num : 439 ∣ 1 + 877 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 439 g439 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 439 g439 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g76913 := S7 76913 (by norm_num) (by norm_num) (by decide) ((by norm_num : 76913 ∣ 1 + 877 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 76913 g76913 (by norm_num)
    · exfalso; have hd := D4 he
      have g7057 := S7 7057 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7057 ∣ 1 + 877 ^ 4).trans hd)
      have g3529 := S1 3529 (by norm_num) (by norm_num) (by decide) 7057 g7057 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 3529 g3529 (by norm_num)
      have g353 := S1 353 (by norm_num) (by norm_num) (by decide) 3529 g3529 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 353 g353 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 881
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 881 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g388081 := S7 388081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 388081 ∣ 1 + 881 ^ 2).trans hd)
      have g3181 := S1 3181 (by norm_num) (by norm_num) (by decide) 388081 g388081 (by norm_num)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 3181 g3181 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 3181 g3181 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g14177 := S7 14177 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14177 ∣ 1 + 881 ^ 4).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 14177 g14177 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 883
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 883 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g77969 := S7 77969 (by norm_num) (by norm_num) (by decide) ((by norm_num : 77969 ∣ 1 + 883 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 883 ^ 2).trans hd) 77969 g77969 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 887
    · exfalso; have hd := D1 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 887 ^ 1).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 887 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 887 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 887 ^ 2).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D4 he
      have g1289 := S7 1289 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1289 ∣ 1 + 887 ^ 4).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 1289 g1289 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1289 g1289 5 g5 (by norm_num) (by norm_num)) (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_900 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 900 ≤ z) (hi : z < 1200)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 2 = 1 → z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ)) ∧
    (e % 4 = 2 → z ∈ ({11, 139, 181, 199, 271} : Finset ℕ)) ∧
    (e % 8 = 4 → z ∈ ({7, 11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D1 : e % 2 = 1 → 1 + z ^ 1 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D2 : e % 4 = 2 → 1 + z ^ 2 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D4 : e % 8 = 4 → 1 + z ^ 4 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have WK : ∀ L : List ℕ, L.Nodup → (∀ x ∈ L, x ∈ P) →
      2 * L.prod ≤ (L.map (fun p => p + 1)).prod → False := fun L h1 h2 h3 => weight_kill hP E h1 h2 h3
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 907
    · exfalso; have hd := D1 he
      have g227 := S7 227 (by norm_num) (by norm_num) (by decide) ((by norm_num : 227 ∣ 1 + 907 ^ 1).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 227 g227 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 227 g227 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 907 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g24097 := S7 24097 (by norm_num) (by norm_num) (by decide) ((by norm_num : 24097 ∣ 1 + 907 ^ 4).trans hd)
      have g12049 := S1 12049 (by norm_num) (by norm_num) (by decide) 24097 g24097 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 12049 g12049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 911
    · exfalso; have hd := D1 he
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 911 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 911 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g349 := S7 349 (by norm_num) (by norm_num) (by decide) ((by norm_num : 349 ∣ 1 + 911 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 349 g349 (by norm_num)
    · exfalso; have hd := D4 he
      have g296801 := S7 296801 (by norm_num) (by norm_num) (by decide) ((by norm_num : 296801 ∣ 1 + 911 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 296801 g296801 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 919
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 919 ^ 1).trans hd)
      have g23 := S7 23 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23 ∣ 1 + 919 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g101 := S7 101 (by norm_num) (by norm_num) (by decide) ((by norm_num : 101 ∣ 1 + 919 ^ 2).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 101 g101 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g356641641361 := S7 356641641361 prime_356641641361 (by norm_num) (by decide) ((by norm_num : 356641641361 ∣ 1 + 919 ^ 4).trans hd)
      have g283 := S1 283 (by norm_num) (by norm_num) (by decide) 356641641361 g356641641361 (by norm_num)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 283 g283 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 929
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 929 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 929 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g431521 := S7 431521 (by norm_num) (by norm_num) (by decide) ((by norm_num : 431521 ∣ 1 + 929 ^ 2).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 431521 g431521 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 431521 g431521 13 g13 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g57697 := S7 57697 (by norm_num) (by norm_num) (by decide) ((by norm_num : 57697 ∣ 1 + 929 ^ 4).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 57697 g57697 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 937
    · exfalso; have hd := D1 he
      have g67 := S7 67 (by norm_num) (by norm_num) (by decide) ((by norm_num : 67 ∣ 1 + 937 ^ 1).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g87797 := S7 87797 (by norm_num) (by norm_num) (by decide) ((by norm_num : 87797 ∣ 1 + 937 ^ 2).trans hd)
      have g14633 := S1 14633 (by norm_num) (by norm_num) (by decide) 87797 g87797 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 14633 g14633 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 937 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 941
    · exfalso; have hd := D1 he
      have g157 := S7 157 (by norm_num) (by norm_num) (by decide) ((by norm_num : 157 ∣ 1 + 941 ^ 1).trans hd)
      have g79 := S1 79 (by norm_num) (by norm_num) (by decide) 157 g157 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 79 g79 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 941 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g34057 := S7 34057 (by norm_num) (by norm_num) (by decide) ((by norm_num : 34057 ∣ 1 + 941 ^ 2).trans hd)
      have g17029 := S1 17029 (by norm_num) (by norm_num) (by decide) 34057 g34057 (by norm_num)
      exact S8 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 941 ^ 2).trans hd) 17029 g17029 (by norm_num)
    · exfalso; have hd := D4 he
      have g132961 := S7 132961 (by norm_num) (by norm_num) (by decide) ((by norm_num : 132961 ∣ 1 + 941 ^ 4).trans hd)
      have g3499 := S1 3499 (by norm_num) (by norm_num) (by decide) 132961 g132961 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 3499 g3499 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 947
    · exfalso; have hd := D1 he
      have g79 := S7 79 (by norm_num) (by norm_num) (by decide) ((by norm_num : 79 ∣ 1 + 947 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 79 g79 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 947 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 947 ^ 2).trans hd)
      have g89681 := S7 89681 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89681 ∣ 1 + 947 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 89681 g89681 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g929 := S7 929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 929 ∣ 1 + 947 ^ 4).trans hd)
      have g2081 := S7 2081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2081 ∣ 1 + 947 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 929 g929 2081 g2081 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 953
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 953 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g90821 := S7 90821 (by norm_num) (by norm_num) (by decide) ((by norm_num : 90821 ∣ 1 + 953 ^ 2).trans hd)
      have g15137 := S1 15137 (by norm_num) (by norm_num) (by decide) 90821 g90821 (by norm_num)
      exact S6 29 (by norm_num) (by norm_num) (by decide) 15137 g15137 (by norm_num)
    · exfalso; have hd := D4 he
      have g3449 := S7 3449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3449 ∣ 1 + 953 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 3449 g3449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 967
    · exfalso; have hd := D1 he
      exact SQ 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 * 11 ∣ 1 + 967 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g7193 := S7 7193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7193 ∣ 1 + 967 ^ 2).trans hd)
      have g109 := S1 109 (by norm_num) (by norm_num) (by decide) 7193 g7193 (by norm_num)
      exact absurd (S3 11 (by norm_num) (by norm_num) (by decide) 7193 g7193 109 g109 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 967 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 971
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 971 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g197 := S7 197 (by norm_num) (by norm_num) (by decide) ((by norm_num : 197 ∣ 1 + 971 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 971 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 977
    · exfalso; have hd := D1 he
      have g163 := S7 163 (by norm_num) (by norm_num) (by decide) ((by norm_num : 163 ∣ 1 + 977 ^ 1).trans hd)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 163 g163 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 977 ^ 1).trans hd) 41 g41 (by norm_num)
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 977 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 977 ^ 4).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 983
    · exfalso; have hd := D1 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 983 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 983 ^ 1).trans hd) 41 g41 (by norm_num)
    · exfalso; have hd := D2 he
      have g7433 := S7 7433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7433 ∣ 1 + 983 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 7433 g7433 (by norm_num)
    · exfalso; have hd := D4 he
      have g14751089 := S7 14751089 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14751089 ∣ 1 + 983 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 14751089 g14751089 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 991
    · simp
    · exfalso; have hd := D2 he
      have g491041 := S7 491041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 491041 ∣ 1 + 991 ^ 2).trans hd)
      have g245521 := S1 245521 (by norm_num) (by norm_num) (by decide) 491041 g491041 (by norm_num)
      have g122761 := S1 122761 (by norm_num) (by norm_num) (by decide) 245521 g245521 (by norm_num)
      have g61381 := S1 61381 (by norm_num) (by norm_num) (by decide) 122761 g122761 (by norm_num)
      have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 61381 g61381 (by norm_num)
      have g653 := S1 653 (by norm_num) (by norm_num) (by decide) 61381 g61381 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 47 g47 653 g653 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 991 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 997
    · exfalso; have hd := D1 he
      have g499 := S7 499 (by norm_num) (by norm_num) (by decide) ((by norm_num : 499 ∣ 1 + 997 ^ 1).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 499 g499 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 997 ^ 2).trans hd)
      have g99401 := S7 99401 (by norm_num) (by norm_num) (by decide) ((by norm_num : 99401 ∣ 1 + 997 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 99401 g99401 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g494026946041 := S7 494026946041 prime_494026946041 (by norm_num) (by decide) ((by norm_num : 494026946041 ∣ 1 + 997 ^ 4).trans hd)
      have g787 := S1 787 (by norm_num) (by norm_num) (by decide) 494026946041 g494026946041 (by norm_num)
      have g197 := S1 197 (by norm_num) (by norm_num) (by decide) 787 g787 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1009
    · exfalso; have hd := D1 he
      have g101 := S7 101 (by norm_num) (by norm_num) (by decide) ((by norm_num : 101 ∣ 1 + 1009 ^ 1).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 101 g101 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g13 := S7 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 1009 ^ 2).trans hd)
      have g39157 := S7 39157 (by norm_num) (by norm_num) (by decide) ((by norm_num : 39157 ∣ 1 + 1009 ^ 2).trans hd)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 13 g13 39157 g39157 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1123217 := S7 1123217 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1123217 ∣ 1 + 1009 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1123217 g1123217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1013
    · exfalso; have hd := D1 he
      exact SQ 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 * 13 ∣ 1 + 1013 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 1013 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
    · exfalso; have hd := D4 he
      have g526511408281 := S7 526511408281 prime_526511408281 (by norm_num) (by decide) ((by norm_num : 526511408281 ∣ 1 + 1013 ^ 4).trans hd)
      have g4315667281 := S1 4315667281 prime_4315667281 (by norm_num) (by decide) 526511408281 g526511408281 (by norm_num)
      have g2157833641 := S1 2157833641 prime_2157833641 (by norm_num) (by decide) 4315667281 g4315667281 (by norm_num)
      exact absurd (S3 61 (by norm_num) (by norm_num) (by decide) 526511408281 g526511408281 2157833641 g2157833641 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1019
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1019 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g39937 := S7 39937 (by norm_num) (by norm_num) (by decide) ((by norm_num : 39937 ∣ 1 + 1019 ^ 2).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 39937 g39937 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      have g1051 := S1 1051 (by norm_num) (by norm_num) (by decide) 39937 g39937 (by norm_num)
      have g263 := S1 263 (by norm_num) (by norm_num) (by decide) 1051 g1051 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 263 g263 (by norm_num) (by norm_num)) (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1021
    · exfalso; have hd := D1 he
      have g7 := S7 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 ∣ 1 + 1021 ^ 1).trans hd)
      have g73 := S7 73 (by norm_num) (by norm_num) (by decide) ((by norm_num : 73 ∣ 1 + 1021 ^ 1).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 73 g73 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      have g3 := S1 3 (by norm_num) (by norm_num) (by decide) 5 g5 (by norm_num)
      exact WK [7, 73, 37, 19, 5, 3] (by decide)
        (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (by norm_num)
    · exfalso; have hd := D2 he
      have g233 := S7 233 (by norm_num) (by norm_num) (by decide) ((by norm_num : 233 ∣ 1 + 1021 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 233 g233 (by norm_num)
    · exfalso; have hd := D4 he
      have g3209 := S7 3209 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3209 ∣ 1 + 1021 ^ 4).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 3209 g3209 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1031
    · exfalso; have hd := D1 he
      have g43 := S7 43 (by norm_num) (by norm_num) (by decide) ((by norm_num : 43 ∣ 1 + 1031 ^ 1).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1031 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g531481 := S7 531481 (by norm_num) (by norm_num) (by decide) ((by norm_num : 531481 ∣ 1 + 1031 ^ 2).trans hd)
      have g37963 := S1 37963 (by norm_num) (by norm_num) (by decide) 531481 g531481 (by norm_num)
      have g9491 := S1 9491 (by norm_num) (by norm_num) (by decide) 37963 g37963 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 531481 g531481 9491 g9491 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 1031 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1033
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 1033 ^ 1).trans hd)
      have g47 := S7 47 (by norm_num) (by norm_num) (by decide) ((by norm_num : 47 ∣ 1 + 1033 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 47 g47 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1033 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g1993 := S7 1993 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1993 ∣ 1 + 1033 ^ 4).trans hd)
      have g997 := S1 997 (by norm_num) (by norm_num) (by decide) 1993 g1993 (by norm_num)
      have g499 := S1 499 (by norm_num) (by norm_num) (by decide) 997 g997 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 499 g499 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1039
    · simp
    · exfalso; have hd := D2 he
      have g539761 := S7 539761 (by norm_num) (by norm_num) (by decide) ((by norm_num : 539761 ∣ 1 + 1039 ^ 2).trans hd)
      have g3697 := S1 3697 (by norm_num) (by norm_num) (by decide) 539761 g539761 (by norm_num)
      exact S6 43 (by norm_num) (by norm_num) (by decide) 3697 g3697 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1039 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1049
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1049 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g7537 := S7 7537 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7537 ∣ 1 + 1049 ^ 2).trans hd)
      have g3769 := S1 3769 (by norm_num) (by norm_num) (by decide) 7537 g7537 (by norm_num)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 3769 g3769 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 3769 g3769 29 g29 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g605441180401 := S7 605441180401 prime_605441180401 (by norm_num) (by decide) ((by norm_num : 605441180401 ∣ 1 + 1049 ^ 4).trans hd)
      have g8181637573 := S1 8181637573 prime_8181637573 (by norm_num) (by decide) 605441180401 g605441180401 (by norm_num)
      have g970999 := S1 970999 (by norm_num) (by norm_num) (by decide) 8181637573 g8181637573 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 970999 g970999 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1051
    · exfalso; have hd := D1 he
      have g263 := S7 263 (by norm_num) (by norm_num) (by decide) ((by norm_num : 263 ∣ 1 + 1051 ^ 1).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 263 g263 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 263 g263 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g552301 := S7 552301 (by norm_num) (by norm_num) (by decide) ((by norm_num : 552301 ∣ 1 + 1051 ^ 2).trans hd)
      have g276151 := S1 276151 (by norm_num) (by norm_num) (by decide) 552301 g552301 (by norm_num)
      have g34519 := S1 34519 (by norm_num) (by norm_num) (by decide) 276151 g276151 (by norm_num)
      have g863 := S1 863 (by norm_num) (by norm_num) (by decide) 34519 g34519 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 863 g863 (by norm_num)
    · exfalso; have hd := D4 he
      have g8934721 := S7 8934721 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8934721 ∣ 1 + 1051 ^ 4).trans hd)
      have g659 := S1 659 (by norm_num) (by norm_num) (by decide) 8934721 g8934721 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 659 g659 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 659 g659 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1061
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1061 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1493 := S7 1493 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1493 ∣ 1 + 1061 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1493 g1493 (by norm_num)
    · exfalso; have hd := D4 he
      have g71777 := S7 71777 (by norm_num) (by norm_num) (by decide) ((by norm_num : 71777 ∣ 1 + 1061 ^ 4).trans hd)
      have g1709 := S1 1709 (by norm_num) (by norm_num) (by decide) 71777 g71777 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1709 g1709 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1063
    · simp
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1063 ^ 2).trans hd)
      have g112997 := S7 112997 (by norm_num) (by norm_num) (by decide) ((by norm_num : 112997 ∣ 1 + 1063 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 112997 g112997 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1063 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1069
    · exfalso; have hd := D1 he
      have g107 := S7 107 (by norm_num) (by norm_num) (by decide) ((by norm_num : 107 ∣ 1 + 1069 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
    · exfalso; have hd := D2 he
      have g571381 := S7 571381 (by norm_num) (by norm_num) (by decide) ((by norm_num : 571381 ∣ 1 + 1069 ^ 2).trans hd)
      have g40813 := S1 40813 (by norm_num) (by norm_num) (by decide) 571381 g571381 (by norm_num)
      have g20407 := S1 20407 (by norm_num) (by norm_num) (by decide) 40813 g40813 (by norm_num)
      have g2551 := S1 2551 (by norm_num) (by norm_num) (by decide) 20407 g20407 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 2551 g2551 (by norm_num)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 2551 g2551 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 29 g29 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1069 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1087
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1087 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g149 := S7 149 (by norm_num) (by norm_num) (by decide) ((by norm_num : 149 ∣ 1 + 1087 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 149 g149 (by norm_num)
    · exfalso; have hd := D4 he
      have g698052650881 := S7 698052650881 prime_698052650881 (by norm_num) (by decide) ((by norm_num : 698052650881 ∣ 1 + 1087 ^ 4).trans hd)
      have g2080423 := S1 2080423 (by norm_num) (by norm_num) (by decide) 698052650881 g698052650881 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 2080423 g2080423 (by norm_num)
      have g13687 := S1 13687 (by norm_num) (by norm_num) (by decide) 2080423 g2080423 (by norm_num)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 13687 g13687 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 19 g19 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1091
    · exfalso; have hd := D1 he
      have g13 := S7 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 1091 ^ 1).trans hd)
      exact S8 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 ∣ 1 + 1091 ^ 1).trans hd) 13 g13 (by norm_num)
    · exfalso; have hd := D2 he
      have g595141 := S7 595141 (by norm_num) (by norm_num) (by decide) ((by norm_num : 595141 ∣ 1 + 1091 ^ 2).trans hd)
      have g337 := S1 337 (by norm_num) (by norm_num) (by decide) 595141 g595141 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D4 he
      have g84401 := S7 84401 (by norm_num) (by norm_num) (by decide) ((by norm_num : 84401 ∣ 1 + 1091 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 84401 g84401 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1093
    · exfalso; have hd := D1 he
      have g547 := S7 547 (by norm_num) (by norm_num) (by decide) ((by norm_num : 547 ∣ 1 + 1093 ^ 1).trans hd)
      have g137 := S1 137 (by norm_num) (by norm_num) (by decide) 547 g547 (by norm_num)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 137 g137 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 137 g137 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1093 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1093 ^ 4).trans hd)
      have g17404710161 := S7 17404710161 prime_17404710161 (by norm_num) (by decide) ((by norm_num : 17404710161 ∣ 1 + 1093 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 41 g41 17404710161 g17404710161 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1097
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1097 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1097 ^ 2).trans hd)
      have g9257 := S7 9257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 9257 ∣ 1 + 1097 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 9257 g9257 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1097 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1103
    · exfalso; have hd := D1 he
      have g23 := S7 23 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23 ∣ 1 + 1103 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1103 ^ 1).trans hd) 23 g23 (by norm_num)
    · exfalso; have hd := D2 he
      have g121661 := S7 121661 (by norm_num) (by norm_num) (by decide) ((by norm_num : 121661 ∣ 1 + 1103 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 121661 g121661 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1103 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1109
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1109 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1109 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1109 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g953 := S7 953 (by norm_num) (by norm_num) (by decide) ((by norm_num : 953 ∣ 1 + 1109 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 953 g953 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1117
    · simp
    · exfalso; have hd := D2 he
      have g124769 := S7 124769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 124769 ∣ 1 + 1117 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1117 ^ 2).trans hd) 124769 g124769 (by norm_num)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1117 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1123
    · exfalso; have hd := D1 he
      have g281 := S7 281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 281 ∣ 1 + 1123 ^ 1).trans hd)
      have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 281 g281 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 281 g281 47 g47 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 1123 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
    · exfalso; have hd := D4 he
      have g795223177321 := S7 795223177321 prime_795223177321 (by norm_num) (by decide) ((by norm_num : 795223177321 ∣ 1 + 1123 ^ 4).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 795223177321 g795223177321 (by norm_num)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 795223177321 g795223177321 37 g37 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1129
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1129 ^ 1).trans hd)
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1129 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 113 g113 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g637321 := S7 637321 (by norm_num) (by norm_num) (by decide) ((by norm_num : 637321 ∣ 1 + 1129 ^ 2).trans hd)
      have g45523 := S1 45523 (by norm_num) (by norm_num) (by decide) 637321 g637321 (by norm_num)
      have g599 := S1 599 (by norm_num) (by norm_num) (by decide) 45523 g45523 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 599 g599 (by norm_num)
    · exfalso; have hd := D4 he
      have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 1129 ^ 4).trans hd)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 353 g353 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 353 g353 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1151
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1151 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g662401 := S7 662401 (by norm_num) (by norm_num) (by decide) ((by norm_num : 662401 ∣ 1 + 1151 ^ 2).trans hd)
      have g349 := S1 349 (by norm_num) (by norm_num) (by decide) 662401 g662401 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 349 g349 (by norm_num)
    · exfalso; have hd := D4 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1151 ^ 4).trans hd)
      have g433 := S7 433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 433 ∣ 1 + 1151 ^ 4).trans hd)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 41 g41 433 g433 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1153
    · exfalso; have hd := D1 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 1153 ^ 1).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
    · exfalso; have hd := D2 he
      have g3593 := S7 3593 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3593 ∣ 1 + 1153 ^ 2).trans hd)
      have g599 := S1 599 (by norm_num) (by norm_num) (by decide) 3593 g3593 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 599 g599 (by norm_num)
    · exfalso; have hd := D4 he
      have g16937 := S7 16937 (by norm_num) (by norm_num) (by decide) ((by norm_num : 16937 ∣ 1 + 1153 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 16937 g16937 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1163
    · exfalso; have hd := D1 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1163 ^ 1).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1163 ^ 2).trans hd)
      have g135257 := S7 135257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 135257 ∣ 1 + 1163 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 135257 g135257 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g914721449881 := S7 914721449881 prime_914721449881 (by norm_num) (by decide) ((by norm_num : 914721449881 ∣ 1 + 1163 ^ 4).trans hd)
      have g499 := S1 499 (by norm_num) (by norm_num) (by decide) 914721449881 g914721449881 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 499 g499 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1171
    · exfalso; have hd := D1 he
      have g293 := S7 293 (by norm_num) (by norm_num) (by decide) ((by norm_num : 293 ∣ 1 + 1171 ^ 1).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 293 g293 (by norm_num)
    · exfalso; have hd := D2 he
      have g685621 := S7 685621 (by norm_num) (by norm_num) (by decide) ((by norm_num : 685621 ∣ 1 + 1171 ^ 2).trans hd)
      have g48973 := S1 48973 (by norm_num) (by norm_num) (by decide) 685621 g685621 (by norm_num)
      have g521 := S1 521 (by norm_num) (by norm_num) (by decide) 48973 g48973 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 521 g521 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1171 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1181
    · exfalso; have hd := D1 he
      have g197 := S7 197 (by norm_num) (by norm_num) (by decide) ((by norm_num : 197 ∣ 1 + 1181 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
    · exfalso; have hd := D2 he
      have g697381 := S7 697381 (by norm_num) (by norm_num) (by decide) ((by norm_num : 697381 ∣ 1 + 1181 ^ 2).trans hd)
      have g109 := S1 109 (by norm_num) (by norm_num) (by decide) 697381 g697381 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 109 g109 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 109 g109 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1181 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1187
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1187 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1187 ^ 2).trans hd)
      have g140897 := S7 140897 (by norm_num) (by norm_num) (by decide) ((by norm_num : 140897 ∣ 1 + 1187 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 140897 g140897 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g929 := S7 929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 929 ∣ 1 + 1187 ^ 4).trans hd)
      have g127913 := S7 127913 (by norm_num) (by norm_num) (by decide) ((by norm_num : 127913 ∣ 1 + 1187 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 929 g929 127913 g127913 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1193
    · exfalso; have hd := D1 he
      have g199 := S7 199 (by norm_num) (by norm_num) (by decide) ((by norm_num : 199 ∣ 1 + 1193 ^ 1).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 199 g199 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1193 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g1601 := S7 1601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1601 ∣ 1 + 1193 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1601 g1601 (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_1200 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1200 ≤ z) (hi : z < 1500)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 2 = 1 → z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ)) ∧
    (e % 4 = 2 → z ∈ ({11, 139, 181, 199, 271} : Finset ℕ)) ∧
    (e % 8 = 4 → z ∈ ({7, 11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D1 : e % 2 = 1 → 1 + z ^ 1 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D2 : e % 4 = 2 → 1 + z ^ 2 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D4 : e % 8 = 4 → 1 + z ^ 4 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have WK : ∀ L : List ℕ, L.Nodup → (∀ x ∈ L, x ∈ P) →
      2 * L.prod ≤ (L.map (fun p => p + 1)).prod → False := fun L h1 h2 h3 => weight_kill hP E h1 h2 h3
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1201
    · simp
    · exfalso; have hd := D2 he
      have g1913 := S7 1913 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1913 ∣ 1 + 1201 ^ 2).trans hd)
      exact S8 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 1201 ^ 2).trans hd) 1913 g1913 (by norm_num)
    · exfalso; have hd := D4 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1201 ^ 4).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1213
    · simp
    · exfalso; have hd := D2 he
      have g147137 := S7 147137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 147137 ∣ 1 + 1213 ^ 2).trans hd)
      have g179 := S1 179 (by norm_num) (by norm_num) (by decide) 147137 g147137 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 179 g179 (by norm_num)
    · exfalso; have hd := D4 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 1213 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1217
    · exfalso; have hd := D1 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 1217 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1217 ^ 1).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D2 he
      have g11393 := S7 11393 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11393 ∣ 1 + 1217 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 11393 g11393 (by norm_num)
    · exfalso; have hd := D4 he
      have g1407337 := S7 1407337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1407337 ∣ 1 + 1217 ^ 4).trans hd)
      have g22699 := S1 22699 (by norm_num) (by norm_num) (by decide) 1407337 g1407337 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 22699 g22699 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1223
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1223 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g373 := S7 373 (by norm_num) (by norm_num) (by decide) ((by norm_num : 373 ∣ 1 + 1223 ^ 2).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 373 g373 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g1726577 := S7 1726577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1726577 ∣ 1 + 1223 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1726577 g1726577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1229
    · exfalso; have hd := D1 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1229 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1229 ^ 1).trans hd) 41 g41 (by norm_num)
    · exfalso; have hd := D2 he
      have g773 := S7 773 (by norm_num) (by norm_num) (by decide) ((by norm_num : 773 ∣ 1 + 1229 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 773 g773 (by norm_num)
    · exfalso; have hd := D4 he
      have g597769 := S7 597769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 597769 ∣ 1 + 1229 ^ 4).trans hd)
      exact S6 23 (by norm_num) (by norm_num) (by decide) 597769 g597769 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1231
    · simp
    · exfalso; have hd := D2 he
      have g12421 := S7 12421 (by norm_num) (by norm_num) (by decide) ((by norm_num : 12421 ∣ 1 + 1231 ^ 2).trans hd)
      have g6211 := S1 6211 (by norm_num) (by norm_num) (by decide) 12421 g12421 (by norm_num)
      have g1553 := S1 1553 (by norm_num) (by norm_num) (by decide) 6211 g6211 (by norm_num)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 1553 g1553 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1553 g1553 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g73 := S7 73 (by norm_num) (by norm_num) (by decide) ((by norm_num : 73 ∣ 1 + 1231 ^ 4).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 73 g73 (by norm_num)
      have g15728212057 := S7 15728212057 prime_15728212057 (by norm_num) (by decide) ((by norm_num : 15728212057 ∣ 1 + 1231 ^ 4).trans hd)
      have g604931233 := S1 604931233 prime_604931233 (by norm_num) (by decide) 15728212057 g15728212057 (by norm_num)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 37 g37 604931233 g604931233 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1237
    · simp
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1237 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 1237 ^ 4).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1249
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1249 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 1249 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1249 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1259
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1259 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 1259 ^ 2).trans hd)
      have g27329 := S7 27329 (by norm_num) (by norm_num) (by decide) ((by norm_num : 27329 ∣ 1 + 1259 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29 g29 27329 g27329 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1256240888281 := S7 1256240888281 prime_1256240888281 (by norm_num) (by decide) ((by norm_num : 1256240888281 ∣ 1 + 1259 ^ 4).trans hd)
      have g379 := S1 379 (by norm_num) (by norm_num) (by decide) 1256240888281 g1256240888281 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 379 g379 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 379 g379 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1277
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1277 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g521 := S7 521 (by norm_num) (by norm_num) (by decide) ((by norm_num : 521 ∣ 1 + 1277 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 521 g521 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1277 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1279
    · simp
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1279 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g2393 := S7 2393 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2393 ∣ 1 + 1279 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2393 g2393 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1283
    · exfalso; have hd := D1 he
      have g107 := S7 107 (by norm_num) (by norm_num) (by decide) ((by norm_num : 107 ∣ 1 + 1283 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
    · exfalso; have hd := D2 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1283 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1283 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1289
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1289 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1289 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 1289 ^ 2).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g22453 := S7 22453 (by norm_num) (by norm_num) (by decide) ((by norm_num : 22453 ∣ 1 + 1289 ^ 2).trans hd)
      have g109 := S1 109 (by norm_num) (by norm_num) (by decide) 22453 g22453 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 19 g19 109 g109 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g953 := S7 953 (by norm_num) (by norm_num) (by decide) ((by norm_num : 953 ∣ 1 + 1289 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 953 g953 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1291
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1291 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g173 := S7 173 (by norm_num) (by norm_num) (by decide) ((by norm_num : 173 ∣ 1 + 1291 ^ 2).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 173 g173 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 173 g173 29 g29 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1601 := S7 1601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1601 ∣ 1 + 1291 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1601 g1601 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1297
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 1297 ^ 1).trans hd)
      have g59 := S7 59 (by norm_num) (by norm_num) (by decide) ((by norm_num : 59 ∣ 1 + 1297 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 59 g59 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g149 := S7 149 (by norm_num) (by norm_num) (by decide) ((by norm_num : 149 ∣ 1 + 1297 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 149 g149 (by norm_num)
    · exfalso; have hd := D4 he
      have g15737 := S7 15737 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15737 ∣ 1 + 1297 ^ 4).trans hd)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 15737 g15737 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 15737 g15737 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1301
    · simp
    · exfalso; have hd := D2 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 1301 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1301 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1303
    · simp
    · exfalso; have hd := D2 he
      exact SQ 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 * 41 ∣ 1 + 1303 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g1297 := S7 1297 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1297 ∣ 1 + 1303 ^ 4).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 1297 g1297 (by norm_num)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 1297 g1297 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1307
    · exfalso; have hd := D1 he
      have g109 := S7 109 (by norm_num) (by norm_num) (by decide) ((by norm_num : 109 ∣ 1 + 1307 ^ 1).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 109 g109 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1307 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1307 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1307 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1319
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 1319 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1319 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g1709 := S7 1709 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1709 ∣ 1 + 1319 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1709 g1709 (by norm_num)
    · exfalso; have hd := D4 he
      have g40361 := S7 40361 (by norm_num) (by norm_num) (by decide) ((by norm_num : 40361 ∣ 1 + 1319 ^ 4).trans hd)
      exact S6 31 (by norm_num) (by norm_num) (by decide) 40361 g40361 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1321
    · simp
    · exfalso; have hd := D2 he
      have g1637 := S7 1637 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1637 ∣ 1 + 1321 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1637 g1637 (by norm_num)
    · exfalso; have hd := D4 he
      have g13001 := S7 13001 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13001 ∣ 1 + 1321 ^ 4).trans hd)
      have g197 := S1 197 (by norm_num) (by norm_num) (by decide) 13001 g13001 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1327
    · simp
    · exfalso; have hd := D2 he
      have g293 := S7 293 (by norm_num) (by norm_num) (by decide) ((by norm_num : 293 ∣ 1 + 1327 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 293 g293 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1361
    · exfalso; have hd := D1 he
      have g227 := S7 227 (by norm_num) (by norm_num) (by decide) ((by norm_num : 227 ∣ 1 + 1361 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1361 ^ 1).trans hd) 227 g227 (by norm_num)
    · exfalso; have hd := D2 he
      have g926161 := S7 926161 (by norm_num) (by norm_num) (by decide) ((by norm_num : 926161 ∣ 1 + 1361 ^ 2).trans hd)
      have g811 := S1 811 (by norm_num) (by norm_num) (by decide) 926161 g926161 (by norm_num)
      have g571 := S1 571 (by norm_num) (by norm_num) (by decide) 926161 g926161 (by norm_num)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 571 g571 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 811 g811 13 g13 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g42433 := S7 42433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 42433 ∣ 1 + 1361 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 42433 g42433 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1367
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1367 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g186869 := S7 186869 (by norm_num) (by norm_num) (by decide) ((by norm_num : 186869 ∣ 1 + 1367 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1367 ^ 2).trans hd) 186869 g186869 (by norm_num)
    · exfalso; have hd := D4 he
      have g42585348521 := S7 42585348521 prime_42585348521 (by norm_num) (by decide) ((by norm_num : 42585348521 ∣ 1 + 1367 ^ 4).trans hd)
      have g2663 := S1 2663 (by norm_num) (by norm_num) (by decide) 42585348521 g42585348521 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2663 g2663 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1373
    · exfalso; have hd := D1 he
      have g229 := S7 229 (by norm_num) (by norm_num) (by decide) ((by norm_num : 229 ∣ 1 + 1373 ^ 1).trans hd)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 229 g229 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1373 ^ 1).trans hd) 23 g23 (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1373 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g4793 := S7 4793 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4793 ∣ 1 + 1373 ^ 4).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 4793 g4793 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1381
    · exfalso; have hd := D1 he
      have g691 := S7 691 (by norm_num) (by norm_num) (by decide) ((by norm_num : 691 ∣ 1 + 1381 ^ 1).trans hd)
      have g173 := S1 173 (by norm_num) (by norm_num) (by decide) 691 g691 (by norm_num)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 173 g173 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 173 g173 29 g29 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1381 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g1818631539961 := S7 1818631539961 prime_1818631539961 (by norm_num) (by decide) ((by norm_num : 1818631539961 ∣ 1 + 1381 ^ 4).trans hd)
      have g735949 := S1 735949 (by norm_num) (by norm_num) (by decide) 1818631539961 g1818631539961 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 735949 g735949 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1399
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1399 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g13 := S7 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 ∣ 1 + 1399 ^ 2).trans hd)
      have g75277 := S7 75277 (by norm_num) (by norm_num) (by decide) ((by norm_num : 75277 ∣ 1 + 1399 ^ 2).trans hd)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 13 g13 75277 g75277 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g28433 := S7 28433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 28433 ∣ 1 + 1399 ^ 4).trans hd)
      have g677 := S1 677 (by norm_num) (by norm_num) (by decide) 28433 g28433 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 28433 g28433 677 g677 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1409
    · exfalso; have hd := D1 he
      have g47 := S7 47 (by norm_num) (by norm_num) (by decide) ((by norm_num : 47 ∣ 1 + 1409 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1409 ^ 1).trans hd) 47 g47 (by norm_num)
    · exfalso; have hd := D2 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 1409 ^ 2).trans hd)
      have g2633 := S7 2633 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2633 ∣ 1 + 1409 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29 g29 2633 g2633 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1409 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1423
    · exfalso; have hd := D1 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 1423 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
    · exfalso; have hd := D2 he
      have g202493 := S7 202493 (by norm_num) (by norm_num) (by decide) ((by norm_num : 202493 ∣ 1 + 1423 ^ 2).trans hd)
      have g33749 := S1 33749 (by norm_num) (by norm_num) (by decide) 202493 g202493 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 33749 g33749 (by norm_num)
    · exfalso; have hd := D4 he
      have g3217 := S7 3217 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3217 ∣ 1 + 1423 ^ 4).trans hd)
      have g1609 := S1 1609 (by norm_num) (by norm_num) (by decide) 3217 g3217 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 1609 g1609 (by norm_num)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 1609 g1609 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 23 g23 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1427
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1427 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g269 := S7 269 (by norm_num) (by norm_num) (by decide) ((by norm_num : 269 ∣ 1 + 1427 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 269 g269 (by norm_num)
    · exfalso; have hd := D4 he
      have g155201 := S7 155201 (by norm_num) (by norm_num) (by decide) ((by norm_num : 155201 ∣ 1 + 1427 ^ 4).trans hd)
      have g13358921 := S7 13358921 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13358921 ∣ 1 + 1427 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 155201 g155201 13358921 g13358921 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1429
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1429 ^ 1).trans hd)
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 1429 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g181 := S7 181 (by norm_num) (by norm_num) (by decide) ((by norm_num : 181 ∣ 1 + 1429 ^ 2).trans hd)
      have g5641 := S7 5641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5641 ∣ 1 + 1429 ^ 2).trans hd)
      exact absurd (S3 13 (by norm_num) (by norm_num) (by decide) 181 g181 5641 g5641 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17929 := S7 17929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17929 ∣ 1 + 1429 ^ 4).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 17929 g17929 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 17929 g17929 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1433
    · exfalso; have hd := D1 he
      have g239 := S7 239 (by norm_num) (by norm_num) (by decide) ((by norm_num : 239 ∣ 1 + 1433 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1433 ^ 1).trans hd) 239 g239 (by norm_num)
    · exfalso; have hd := D2 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1433 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D4 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 1433 ^ 4).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1439
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1439 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1035361 := S7 1035361 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1035361 ∣ 1 + 1439 ^ 2).trans hd)
      have g487 := S1 487 (by norm_num) (by norm_num) (by decide) 1035361 g1035361 (by norm_num)
      have g1063 := S1 1063 (by norm_num) (by norm_num) (by decide) 1035361 g1035361 (by norm_num)
      have g61 := S1 61 (by norm_num) (by norm_num) (by decide) 487 g487 (by norm_num)
      have g7 := S1 7 (by norm_num) (by norm_num) (by decide) 1063 g1063 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 1063 g1063 (by norm_num)
      have g31 := S1 31 (by norm_num) (by norm_num) (by decide) 61 g61 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      have g3 := S1 3 (by norm_num) (by norm_num) (by decide) 5 g5 (by norm_num)
      exact WK [1035361, 487, 1063, 61, 7, 19, 31, 5, 3] (by decide)
        (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (by norm_num)
    · exfalso; have hd := D4 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 1439 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1447
    · exfalso; have hd := D1 he
      have g181 := S7 181 (by norm_num) (by norm_num) (by decide) ((by norm_num : 181 ∣ 1 + 1447 ^ 1).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 181 g181 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1447 ^ 2).trans hd)
      have g209381 := S7 209381 (by norm_num) (by norm_num) (by decide) ((by norm_num : 209381 ∣ 1 + 1447 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 209381 g209381 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g149417 := S7 149417 (by norm_num) (by norm_num) (by decide) ((by norm_num : 149417 ∣ 1 + 1447 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 149417 g149417 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1451
    · exfalso; have hd := D1 he
      exact SQ 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 * 11 ∣ 1 + 1451 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 * 13 ∣ 1 + 1451 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1451 ^ 4).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 113 g113 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1453
    · exfalso; have hd := D1 he
      have g727 := S7 727 (by norm_num) (by norm_num) (by decide) ((by norm_num : 727 ∣ 1 + 1453 ^ 1).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 727 g727 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 727 g727 13 g13 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g3461 := S7 3461 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3461 ∣ 1 + 1453 ^ 2).trans hd)
      have g577 := S1 577 (by norm_num) (by norm_num) (by decide) 3461 g3461 (by norm_num)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1453 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1459
    · exfalso; have hd := D1 he
      have g73 := S7 73 (by norm_num) (by norm_num) (by decide) ((by norm_num : 73 ∣ 1 + 1459 ^ 1).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 73 g73 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1459 ^ 1).trans hd) 19 g19 (by norm_num)
    · exfalso; have hd := D2 he
      have g1064341 := S7 1064341 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1064341 ∣ 1 + 1459 ^ 2).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 1064341 g1064341 (by norm_num)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 1064341 g1064341 37 g37 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 1459 ^ 4).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1471
    · simp
    · exfalso; have hd := D2 he
      have g317 := S7 317 (by norm_num) (by norm_num) (by decide) ((by norm_num : 317 ∣ 1 + 1471 ^ 2).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 317 g317 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1471 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1481
    · exfalso; have hd := D1 he
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 1481 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1481 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g229 := S7 229 (by norm_num) (by norm_num) (by decide) ((by norm_num : 229 ∣ 1 + 1481 ^ 2).trans hd)
      have g4789 := S7 4789 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4789 ∣ 1 + 1481 ^ 2).trans hd)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 229 g229 4789 g4789 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1481 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1483
    · exfalso; have hd := D1 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 1483 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 1483 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g2418436052761 := S7 2418436052761 prime_2418436052761 (by norm_num) (by decide) ((by norm_num : 2418436052761 ∣ 1 + 1483 ^ 4).trans hd)
      have g2239 := S1 2239 (by norm_num) (by norm_num) (by decide) 2418436052761 g2418436052761 (by norm_num)
      have g540070579 := S1 540070579 prime_540070579 (by norm_num) (by decide) 2418436052761 g2418436052761 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 2239 g2239 540070579 g540070579 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1487
    · simp
    · exfalso; have hd := D2 he
      have g233 := S7 233 (by norm_num) (by norm_num) (by decide) ((by norm_num : 233 ∣ 1 + 1487 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 233 g233 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1487 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1489
    · exfalso; have hd := D1 he
      have g149 := S7 149 (by norm_num) (by norm_num) (by decide) ((by norm_num : 149 ∣ 1 + 1489 ^ 1).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 149 g149 (by norm_num)
    · exfalso; have hd := D2 he
      have g1108561 := S7 1108561 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1108561 ∣ 1 + 1489 ^ 2).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 1108561 g1108561 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 1108561 g1108561 13 g13 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1721 := S7 1721 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1721 ∣ 1 + 1489 ^ 4).trans hd)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 1721 g1721 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1721 g1721 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1493
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1493 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1493 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g2484329722201 := S7 2484329722201 prime_2484329722201 (by norm_num) (by decide) ((by norm_num : 2484329722201 ∣ 1 + 1493 ^ 4).trans hd)
      have g33572023273 := S1 33572023273 prime_33572023273 (by norm_num) (by decide) 2484329722201 g2484329722201 (by norm_num)
      have g173 := S1 173 (by norm_num) (by norm_num) (by decide) 33572023273 g33572023273 (by norm_num)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 173 g173 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 173 g173 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1499
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1499 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1123501 := S7 1123501 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1123501 ∣ 1 + 1499 ^ 2).trans hd)
      have g18121 := S1 18121 (by norm_num) (by norm_num) (by decide) 1123501 g1123501 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 18121 g18121 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g12546689 := S7 12546689 (by norm_num) (by norm_num) (by decide) ((by norm_num : 12546689 ∣ 1 + 1499 ^ 4).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 12546689 g12546689 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_1500 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1500 ≤ z) (hi : z < 1800)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 2 = 1 → z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ)) ∧
    (e % 4 = 2 → z ∈ ({11, 139, 181, 199, 271} : Finset ℕ)) ∧
    (e % 8 = 4 → z ∈ ({7, 11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D1 : e % 2 = 1 → 1 + z ^ 1 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D2 : e % 4 = 2 → 1 + z ^ 2 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D4 : e % 8 = 4 → 1 + z ^ 4 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have WK : ∀ L : List ℕ, L.Nodup → (∀ x ∈ L, x ∈ P) →
      2 * L.prod ≤ (L.map (fun p => p + 1)).prod → False := fun L h1 h2 h3 => weight_kill hP E h1 h2 h3
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1511
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1511 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 1511 ^ 2).trans hd)
      have g30853 := S7 30853 (by norm_num) (by norm_num) (by decide) ((by norm_num : 30853 ∣ 1 + 1511 ^ 2).trans hd)
      have g15427 := S1 15427 (by norm_num) (by norm_num) (by decide) 30853 g30853 (by norm_num)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 37 g37 15427 g15427 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1511 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1523
    · simp
    · exfalso; have hd := D2 he
      have g6269 := S7 6269 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6269 ∣ 1 + 1523 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1523 ^ 2).trans hd) 6269 g6269 (by norm_num)
    · exfalso; have hd := D4 he
      have g206081 := S7 206081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 206081 ∣ 1 + 1523 ^ 4).trans hd)
      exact S6 107 (by norm_num) (by norm_num) (by decide) 206081 g206081 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1531
    · simp
    · exfalso; have hd := D2 he
      have g1171981 := S7 1171981 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1171981 ∣ 1 + 1531 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 1171981 g1171981 (by norm_num)
    · exfalso; have hd := D4 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1531 ^ 4).trans hd)
      have g8642057 := S7 8642057 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8642057 ∣ 1 + 1531 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 41 g41 8642057 g8642057 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1543
    · exfalso; have hd := D1 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1543 ^ 1).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1543 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g881 := S7 881 (by norm_num) (by norm_num) (by decide) ((by norm_num : 881 ∣ 1 + 1543 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 881 g881 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1549
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1549 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 1549 ^ 2).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 29 g29 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29 g29 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1549 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1553
    · exfalso; have hd := D1 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 1553 ^ 1).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1553 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g557 := S7 557 (by norm_num) (by norm_num) (by decide) ((by norm_num : 557 ∣ 1 + 1553 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 557 g557 (by norm_num)
    · exfalso; have hd := D4 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1553 ^ 4).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1559
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1559 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1559 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g11149 := S7 11149 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11149 ∣ 1 + 1559 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 11149 g11149 (by norm_num)
    · exfalso; have hd := D4 he
      have g8849 := S7 8849 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8849 ∣ 1 + 1559 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 8849 g8849 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1567
    · exfalso; have hd := D1 he
      exact SQ 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 * 7 ∣ 1 + 1567 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 1567 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g3014713114561 := S7 3014713114561 prime_3014713114561 (by norm_num) (by decide) ((by norm_num : 3014713114561 ∣ 1 + 1567 ^ 4).trans hd)
      have g2293 := S1 2293 (by norm_num) (by norm_num) (by decide) 3014713114561 g3014713114561 (by norm_num)
      exact absurd (S3 37 (by norm_num) (by norm_num) (by decide) 3014713114561 g3014713114561 2293 g2293 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1571
    · exfalso; have hd := D1 he
      have g131 := S7 131 (by norm_num) (by norm_num) (by decide) ((by norm_num : 131 ∣ 1 + 1571 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1571 ^ 1).trans hd) 131 g131 (by norm_num)
    · exfalso; have hd := D2 he
      have g541 := S7 541 (by norm_num) (by norm_num) (by decide) ((by norm_num : 541 ∣ 1 + 1571 ^ 2).trans hd)
      have g271 := S1 271 (by norm_num) (by norm_num) (by decide) 541 g541 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 271 g271 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g3045613188841 := S7 3045613188841 prime_3045613188841 (by norm_num) (by decide) ((by norm_num : 3045613188841 ∣ 1 + 1571 ^ 4).trans hd)
      have g1021 := S1 1021 (by norm_num) (by norm_num) (by decide) 3045613188841 g3045613188841 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 3045613188841 g3045613188841 1021 g1021 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1579
    · exfalso; have hd := D1 he
      have g79 := S7 79 (by norm_num) (by norm_num) (by decide) ((by norm_num : 79 ∣ 1 + 1579 ^ 1).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1579 ^ 1).trans hd) 79 g79 (by norm_num)
    · exfalso; have hd := D2 he
      have g17077 := S7 17077 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17077 ∣ 1 + 1579 ^ 2).trans hd)
      have g8539 := S1 8539 (by norm_num) (by norm_num) (by decide) 17077 g17077 (by norm_num)
      have g73 := S7 73 (by norm_num) (by norm_num) (by decide) ((by norm_num : 73 ∣ 1 + 1579 ^ 2).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 73 g73 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 8539 g8539 19 g19 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 1579 ^ 4).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1583
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1583 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g8641 := S7 8641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8641 ∣ 1 + 1583 ^ 2).trans hd)
      exact S8 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 1583 ^ 2).trans hd) 8641 g8641 (by norm_num)
    · exfalso; have hd := D4 he
      have g1097 := S7 1097 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1097 ∣ 1 + 1583 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1097 g1097 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1597
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1597 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 1597 ^ 2).trans hd)
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1597 ^ 2).trans hd)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 37 g37 113 g113 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g281 := S7 281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 281 ∣ 1 + 1597 ^ 4).trans hd)
      have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 281 g281 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 281 g281 47 g47 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1601
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1601 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1693 := S7 1693 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1693 ∣ 1 + 1601 ^ 2).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 1693 g1693 (by norm_num)
    · exfalso; have hd := D4 he
      have g21169 := S7 21169 (by norm_num) (by norm_num) (by decide) ((by norm_num : 21169 ∣ 1 + 1601 ^ 4).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 21169 g21169 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 21169 g21169 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1607
    · exfalso; have hd := D1 he
      have g67 := S7 67 (by norm_num) (by norm_num) (by decide) ((by norm_num : 67 ∣ 1 + 1607 ^ 1).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1607 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1607 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1609
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1609 ^ 1).trans hd)
      have g23 := S7 23 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23 ∣ 1 + 1609 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g349 := S7 349 (by norm_num) (by norm_num) (by decide) ((by norm_num : 349 ∣ 1 + 1609 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 349 g349 (by norm_num)
    · exfalso; have hd := D4 he
      have g1817177 := S7 1817177 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1817177 ∣ 1 + 1609 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 1817177 g1817177 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1613
    · exfalso; have hd := D1 he
      have g269 := S7 269 (by norm_num) (by norm_num) (by decide) ((by norm_num : 269 ∣ 1 + 1613 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 269 g269 (by norm_num)
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 1613 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1613 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1619
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1619 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1619 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g233 := S7 233 (by norm_num) (by norm_num) (by decide) ((by norm_num : 233 ∣ 1 + 1619 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 233 g233 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1621
    · exfalso; have hd := D1 he
      have g811 := S7 811 (by norm_num) (by norm_num) (by decide) ((by norm_num : 811 ∣ 1 + 1621 ^ 1).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 811 g811 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 29 g29 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29 g29 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g569 := S7 569 (by norm_num) (by norm_num) (by decide) ((by norm_num : 569 ∣ 1 + 1621 ^ 2).trans hd)
      have g2309 := S7 2309 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2309 ∣ 1 + 1621 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 569 g569 2309 g2309 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g29153 := S7 29153 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29153 ∣ 1 + 1621 ^ 4).trans hd)
      have g259121 := S7 259121 (by norm_num) (by norm_num) (by decide) ((by norm_num : 259121 ∣ 1 + 1621 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29153 g29153 259121 g259121 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1627
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 1627 ^ 1).trans hd)
      have g37 := S7 37 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37 ∣ 1 + 1627 ^ 1).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 37 g37 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1627 ^ 2).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D4 he
      have g15217 := S7 15217 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15217 ∣ 1 + 1627 ^ 4).trans hd)
      have g1087 := S1 1087 (by norm_num) (by norm_num) (by decide) 15217 g15217 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 1087 g1087 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1637
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1637 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1549 := S7 1549 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1549 ∣ 1 + 1637 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1549 g1549 (by norm_num)
    · exfalso; have hd := D4 he
      have g1049 := S7 1049 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1049 ∣ 1 + 1637 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1049 g1049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1657
    · exfalso; have hd := D1 he
      have g829 := S7 829 (by norm_num) (by norm_num) (by decide) ((by norm_num : 829 ∣ 1 + 1657 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 829 g829 (by norm_num)
      have g83 := S1 83 (by norm_num) (by norm_num) (by decide) 829 g829 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 83 g83 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1657 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 1657 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1663
    · simp
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1663 ^ 2).trans hd)
      have g276557 := S7 276557 (by norm_num) (by norm_num) (by decide) ((by norm_num : 276557 ∣ 1 + 1663 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 276557 g276557 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g258113 := S7 258113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 258113 ∣ 1 + 1663 ^ 4).trans hd)
      have g43019 := S1 43019 (by norm_num) (by norm_num) (by decide) 258113 g258113 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 43019 g43019 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1667
    · exfalso; have hd := D1 he
      have g139 := S7 139 (by norm_num) (by norm_num) (by decide) ((by norm_num : 139 ∣ 1 + 1667 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 139 g139 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1667 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g277889 := S7 277889 (by norm_num) (by norm_num) (by decide) ((by norm_num : 277889 ∣ 1 + 1667 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1667 ^ 2).trans hd) 277889 g277889 (by norm_num)
    · exfalso; have hd := D4 he
      have g409 := S7 409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 409 ∣ 1 + 1667 ^ 4).trans hd)
      exact S8 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1667 ^ 4).trans hd) 409 g409 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1669
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1669 ^ 1).trans hd)
      have g167 := S7 167 (by norm_num) (by norm_num) (by decide) ((by norm_num : 167 ∣ 1 + 1669 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 167 g167 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g107137 := S7 107137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 107137 ∣ 1 + 1669 ^ 2).trans hd)
      have g53569 := S1 53569 (by norm_num) (by norm_num) (by decide) 107137 g107137 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 53569 g53569 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 53569 g53569 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g48473 := S7 48473 (by norm_num) (by norm_num) (by decide) ((by norm_num : 48473 ∣ 1 + 1669 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 48473 g48473 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1693
    · exfalso; have hd := D1 he
      exact SQ 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 * 11 ∣ 1 + 1693 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1693 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g37537 := S7 37537 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37537 ∣ 1 + 1693 ^ 4).trans hd)
      exact S6 137 (by norm_num) (by norm_num) (by decide) 37537 g37537 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1697
    · exfalso; have hd := D1 he
      have g283 := S7 283 (by norm_num) (by norm_num) (by decide) ((by norm_num : 283 ∣ 1 + 1697 ^ 1).trans hd)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 283 g283 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1697 ^ 2).trans hd)
      have g4721 := S7 4721 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4721 ∣ 1 + 1697 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 4721 g4721 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g303073 := S7 303073 (by norm_num) (by norm_num) (by decide) ((by norm_num : 303073 ∣ 1 + 1697 ^ 4).trans hd)
      have g151537 := S1 151537 (by norm_num) (by norm_num) (by decide) 303073 g303073 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 151537 g151537 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1699
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1699 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g317 := S7 317 (by norm_num) (by norm_num) (by decide) ((by norm_num : 317 ∣ 1 + 1699 ^ 2).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 317 g317 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1699 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1709
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1709 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1460341 := S7 1460341 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1460341 ∣ 1 + 1709 ^ 2).trans hd)
      have g56167 := S1 56167 (by norm_num) (by norm_num) (by decide) 1460341 g1460341 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 56167 g56167 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1709 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1721
    · exfalso; have hd := D1 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1721 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1721 ^ 1).trans hd) 41 g41 (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1721 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g36713 := S7 36713 (by norm_num) (by norm_num) (by decide) ((by norm_num : 36713 ∣ 1 + 1721 ^ 4).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 36713 g36713 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 36713 g36713 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1723
    · exfalso; have hd := D1 he
      have g431 := S7 431 (by norm_num) (by norm_num) (by decide) ((by norm_num : 431 ∣ 1 + 1723 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 431 g431 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 * 29 ∣ 1 + 1723 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g60257 := S7 60257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 60257 ∣ 1 + 1723 ^ 4).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 60257 g60257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1733
    · exfalso; have hd := D1 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 1733 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g8117 := S7 8117 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8117 ∣ 1 + 1733 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 8117 g8117 (by norm_num)
    · exfalso; have hd := D4 he
      have g389569 := S7 389569 (by norm_num) (by norm_num) (by decide) ((by norm_num : 389569 ∣ 1 + 1733 ^ 4).trans hd)
      have g11576569 := S7 11576569 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11576569 ∣ 1 + 1733 ^ 4).trans hd)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 389569 g389569 11576569 g11576569 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1741
    · exfalso; have hd := D1 he
      have g67 := S7 67 (by norm_num) (by norm_num) (by decide) ((by norm_num : 67 ∣ 1 + 1741 ^ 1).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g1515541 := S7 1515541 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1515541 ∣ 1 + 1741 ^ 2).trans hd)
      have g103 := S1 103 (by norm_num) (by norm_num) (by decide) 1515541 g1515541 (by norm_num)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 103 g103 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 1515541 g1515541 13 g13 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g3457 := S7 3457 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3457 ∣ 1 + 1741 ^ 4).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 3457 g3457 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 3457 g3457 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1747
    · exfalso; have hd := D1 he
      have g23 := S7 23 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23 ∣ 1 + 1747 ^ 1).trans hd)
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 1747 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 23 g23 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1747 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g42490849 := S7 42490849 (by norm_num) (by norm_num) (by decide) ((by norm_num : 42490849 ∣ 1 + 1747 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 42490849 g42490849 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1753
    · exfalso; have hd := D1 he
      have g877 := S7 877 (by norm_num) (by norm_num) (by decide) ((by norm_num : 877 ∣ 1 + 1753 ^ 1).trans hd)
      have g439 := S1 439 (by norm_num) (by norm_num) (by decide) 877 g877 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 439 g439 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 439 g439 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1753 ^ 2).trans hd)
      have g307301 := S7 307301 (by norm_num) (by norm_num) (by decide) ((by norm_num : 307301 ∣ 1 + 1753 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 307301 g307301 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1753 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1759
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1759 ^ 1).trans hd)
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 1759 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g197 := S7 197 (by norm_num) (by norm_num) (by decide) ((by norm_num : 197 ∣ 1 + 1759 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1759 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1777
    · simp
    · exfalso; have hd := D2 he
      have g2897 := S7 2897 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2897 ∣ 1 + 1777 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2897 g2897 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1777 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1783
    · simp
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1783 ^ 2).trans hd)
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 1783 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 257 g257 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1783 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1787
    · exfalso; have hd := D1 he
      have g149 := S7 149 (by norm_num) (by norm_num) (by decide) ((by norm_num : 149 ∣ 1 + 1787 ^ 1).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 149 g149 (by norm_num)
    · exfalso; have hd := D2 he
      have g197 := S7 197 (by norm_num) (by norm_num) (by decide) ((by norm_num : 197 ∣ 1 + 1787 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1787 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1789
    · exfalso; have hd := D1 he
      have g179 := S7 179 (by norm_num) (by norm_num) (by decide) ((by norm_num : 179 ∣ 1 + 1789 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 179 g179 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 * 13 ∣ 1 + 1789 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g5121667335721 := S7 5121667335721 prime_5121667335721 (by norm_num) (by decide) ((by norm_num : 5121667335721 ∣ 1 + 1789 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 5121667335721 g5121667335721 (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_1800 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1800 ≤ z) (hi : z < 2100)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 2 = 1 → z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ)) ∧
    (e % 4 = 2 → z ∈ ({11, 139, 181, 199, 271} : Finset ℕ)) ∧
    (e % 8 = 4 → z ∈ ({7, 11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D1 : e % 2 = 1 → 1 + z ^ 1 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D2 : e % 4 = 2 → 1 + z ^ 2 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D4 : e % 8 = 4 → 1 + z ^ 4 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have WK : ∀ L : List ℕ, L.Nodup → (∀ x ∈ L, x ∈ P) →
      2 * L.prod ≤ (L.map (fun p => p + 1)).prod → False := fun L h1 h2 h3 => weight_kill hP E h1 h2 h3
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1801
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1801 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g269 := S7 269 (by norm_num) (by norm_num) (by decide) ((by norm_num : 269 ∣ 1 + 1801 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 269 g269 (by norm_num)
    · exfalso; have hd := D4 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1801 ^ 4).trans hd)
      have g128304237161 := S7 128304237161 prime_128304237161 (by norm_num) (by decide) ((by norm_num : 128304237161 ∣ 1 + 1801 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 41 g41 128304237161 g128304237161 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1811
    · exfalso; have hd := D1 he
      have g151 := S7 151 (by norm_num) (by norm_num) (by decide) ((by norm_num : 151 ∣ 1 + 1811 ^ 1).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 151 g151 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1811 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g1639861 := S7 1639861 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1639861 ∣ 1 + 1811 ^ 2).trans hd)
      have g117133 := S1 117133 (by norm_num) (by norm_num) (by decide) 1639861 g1639861 (by norm_num)
      have g58567 := S1 58567 (by norm_num) (by norm_num) (by decide) 117133 g117133 (by norm_num)
      have g7321 := S1 7321 (by norm_num) (by norm_num) (by decide) 58567 g58567 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 1639861 g1639861 7321 g7321 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1811 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1823
    · exfalso; have hd := D1 he
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 1823 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1823 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1823 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g5522257821121 := S7 5522257821121 prime_5522257821121 (by norm_num) (by decide) ((by norm_num : 5522257821121 ∣ 1 + 1823 ^ 4).trans hd)
      have g1768321 := S1 1768321 (by norm_num) (by norm_num) (by decide) 5522257821121 g5522257821121 (by norm_num)
      have g617 := S1 617 (by norm_num) (by norm_num) (by decide) 1768321 g1768321 (by norm_num)
      have g1433 := S1 1433 (by norm_num) (by norm_num) (by decide) 1768321 g1768321 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 617 g617 1433 g1433 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1831
    · exfalso; have hd := D1 he
      have g229 := S7 229 (by norm_num) (by norm_num) (by decide) ((by norm_num : 229 ∣ 1 + 1831 ^ 1).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 229 g229 (by norm_num)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 229 g229 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g1676281 := S7 1676281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1676281 ∣ 1 + 1831 ^ 2).trans hd)
      have g838141 := S1 838141 (by norm_num) (by norm_num) (by decide) 1676281 g1676281 (by norm_num)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 838141 g838141 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1831 ^ 4).trans hd)
      have g137069088521 := S7 137069088521 prime_137069088521 (by norm_num) (by decide) ((by norm_num : 137069088521 ∣ 1 + 1831 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 41 g41 137069088521 g137069088521 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1847
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 1847 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1847 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1847 ^ 2).trans hd)
      have g341141 := S7 341141 (by norm_num) (by norm_num) (by decide) ((by norm_num : 341141 ∣ 1 + 1847 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 341141 g341141 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g8537041 := S7 8537041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8537041 ∣ 1 + 1847 ^ 4).trans hd)
      have g271 := S1 271 (by norm_num) (by norm_num) (by decide) 8537041 g8537041 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 271 g271 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1861
    · exfalso; have hd := D1 he
      exact SQ 7 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7 * 7 ∣ 1 + 1861 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1229 := S7 1229 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1229 ∣ 1 + 1861 ^ 2).trans hd)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 1229 g1229 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1229 g1229 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1861 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1867
    · exfalso; have hd := D1 he
      have g467 := S7 467 (by norm_num) (by norm_num) (by decide) ((by norm_num : 467 ∣ 1 + 1867 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 467 g467 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1867 ^ 2).trans hd)
      have g26813 := S7 26813 (by norm_num) (by norm_num) (by decide) ((by norm_num : 26813 ∣ 1 + 1867 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 26813 g26813 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g563081 := S7 563081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 563081 ∣ 1 + 1867 ^ 4).trans hd)
      have g7219 := S1 7219 (by norm_num) (by norm_num) (by decide) 563081 g563081 (by norm_num)
      exact S6 19 (by norm_num) (by norm_num) (by decide) 7219 g7219 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1871
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1871 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g23977 := S7 23977 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23977 ∣ 1 + 1871 ^ 2).trans hd)
      have g73 := S7 73 (by norm_num) (by norm_num) (by decide) ((by norm_num : 73 ∣ 1 + 1871 ^ 2).trans hd)
      have g37 := S1 37 (by norm_num) (by norm_num) (by decide) 73 g73 (by norm_num)
      exact absurd (S3 19 (by norm_num) (by norm_num) (by decide) 23977 g23977 37 g37 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1873513 := S7 1873513 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1873513 ∣ 1 + 1871 ^ 4).trans hd)
      have g1049 := S1 1049 (by norm_num) (by norm_num) (by decide) 1873513 g1873513 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1049 g1049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1873
    · exfalso; have hd := D1 he
      have g937 := S7 937 (by norm_num) (by norm_num) (by decide) ((by norm_num : 937 ∣ 1 + 1873 ^ 1).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 937 g937 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 1873 ^ 2).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1873 ^ 2).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D4 he
      have g19659695017 := S7 19659695017 prime_19659695017 (by norm_num) (by decide) ((by norm_num : 19659695017 ∣ 1 + 1873 ^ 4).trans hd)
      have g241 := S1 241 (by norm_num) (by norm_num) (by decide) 19659695017 g19659695017 (by norm_num)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1877
    · exfalso; have hd := D1 he
      have g313 := S7 313 (by norm_num) (by norm_num) (by decide) ((by norm_num : 313 ∣ 1 + 1877 ^ 1).trans hd)
      have g157 := S1 157 (by norm_num) (by norm_num) (by decide) 313 g313 (by norm_num)
      have g79 := S1 79 (by norm_num) (by norm_num) (by decide) 157 g157 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 79 g79 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1877 ^ 1).trans hd) 5 g5 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1877 ^ 2).trans hd)
      have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 1877 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1877 ^ 4).trans hd)
      have g137 := S7 137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 137 ∣ 1 + 1877 ^ 4).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 137 g137 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1879
    · exfalso; have hd := D1 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1879 ^ 1).trans hd)
      have g47 := S7 47 (by norm_num) (by norm_num) (by decide) ((by norm_num : 47 ∣ 1 + 1879 ^ 1).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 47 g47 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D2 he
      have g277 := S7 277 (by norm_num) (by norm_num) (by decide) ((by norm_num : 277 ∣ 1 + 1879 ^ 2).trans hd)
      have g139 := S1 139 (by norm_num) (by norm_num) (by decide) 277 g277 (by norm_num)
      have g6373 := S7 6373 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6373 ∣ 1 + 1879 ^ 2).trans hd)
      have g3187 := S1 3187 (by norm_num) (by norm_num) (by decide) 6373 g6373 (by norm_num)
      have g797 := S1 797 (by norm_num) (by norm_num) (by decide) 3187 g3187 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 g139 797 g797 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1879 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1889
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1889 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1069 := S7 1069 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1069 ∣ 1 + 1889 ^ 2).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 1069 g1069 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
    · exfalso; have hd := D4 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 1889 ^ 4).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1901
    · exfalso; have hd := D1 he
      have g317 := S7 317 (by norm_num) (by norm_num) (by decide) ((by norm_num : 317 ∣ 1 + 1901 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1901 ^ 1).trans hd) 317 g317 (by norm_num)
    · exfalso; have hd := D2 he
      have g1806901 := S7 1806901 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1806901 ∣ 1 + 1901 ^ 2).trans hd)
      have g903451 := S1 903451 (by norm_num) (by norm_num) (by decide) 1806901 g1806901 (by norm_num)
      have g20533 := S1 20533 (by norm_num) (by norm_num) (by decide) 903451 g903451 (by norm_num)
      have g10267 := S1 10267 (by norm_num) (by norm_num) (by decide) 20533 g20533 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 10267 g10267 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g54673 := S7 54673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 54673 ∣ 1 + 1901 ^ 4).trans hd)
      have g27337 := S1 27337 (by norm_num) (by norm_num) (by decide) 54673 g54673 (by norm_num)
      have g13669 := S1 13669 (by norm_num) (by norm_num) (by decide) 27337 g27337 (by norm_num)
      have g1367 := S1 1367 (by norm_num) (by norm_num) (by decide) 13669 g13669 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1367 g1367 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1907
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1907 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1907 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      exact SQ 281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 281 * 281 ∣ 1 + 1907 ^ 4).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1913
    · exfalso; have hd := D1 he
      have g11 := S7 11 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11 ∣ 1 + 1913 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1913 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g1249 := S7 1249 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1249 ∣ 1 + 1913 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1249 g1249 (by norm_num)
    · exfalso; have hd := D4 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 1913 ^ 4).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1931
    · exfalso; have hd := D1 he
      have g23 := S7 23 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23 ∣ 1 + 1931 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1931 ^ 1).trans hd) 23 g23 (by norm_num)
    · exfalso; have hd := D2 he
      have g53 := S7 53 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53 ∣ 1 + 1931 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g10133729 := S7 10133729 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10133729 ∣ 1 + 1931 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 10133729 g10133729 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1933
    · exfalso; have hd := D1 he
      have g967 := S7 967 (by norm_num) (by norm_num) (by decide) ((by norm_num : 967 ∣ 1 + 1933 ^ 1).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 967 g967 (by norm_num)
    · exfalso; have hd := D2 he
      have g373649 := S7 373649 (by norm_num) (by norm_num) (by decide) ((by norm_num : 373649 ∣ 1 + 1933 ^ 2).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 373649 g373649 (by norm_num)
    · exfalso; have hd := D4 he
      have g11833 := S7 11833 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11833 ∣ 1 + 1933 ^ 4).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 11833 g11833 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1949
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1949 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1899301 := S7 1899301 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1899301 ∣ 1 + 1949 ^ 2).trans hd)
      have g949651 := S1 949651 (by norm_num) (by norm_num) (by decide) 1899301 g1899301 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 949651 g949651 (by norm_num)
      have g113 := S1 113 (by norm_num) (by norm_num) (by decide) 949651 g949651 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 113 g113 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g98831298337 := S7 98831298337 prime_98831298337 (by norm_num) (by decide) ((by norm_num : 98831298337 ∣ 1 + 1949 ^ 4).trans hd)
      have g36067 := S1 36067 (by norm_num) (by norm_num) (by decide) 98831298337 g98831298337 (by norm_num)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 36067 g36067 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1951
    · simp
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1951 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g131849 := S7 131849 (by norm_num) (by norm_num) (by decide) ((by norm_num : 131849 ∣ 1 + 1951 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 131849 g131849 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1973
    · exfalso; have hd := D1 he
      have g47 := S7 47 (by norm_num) (by norm_num) (by decide) ((by norm_num : 47 ∣ 1 + 1973 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 1973 ^ 1).trans hd) 47 g47 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1973 ^ 2).trans hd)
      have g389273 := S7 389273 (by norm_num) (by norm_num) (by decide) ((by norm_num : 389273 ∣ 1 + 1973 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 389273 g389273 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1973 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1979
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1979 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g941 := S7 941 (by norm_num) (by norm_num) (by decide) ((by norm_num : 941 ∣ 1 + 1979 ^ 2).trans hd)
      have g2081 := S7 2081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2081 ∣ 1 + 1979 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 941 g941 2081 g2081 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g285281 := S7 285281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 285281 ∣ 1 + 1979 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 285281 g285281 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1987
    · exfalso; have hd := D1 he
      have g71 := S7 71 (by norm_num) (by norm_num) (by decide) ((by norm_num : 71 ∣ 1 + 1987 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
    · exfalso; have hd := D2 he
      have g394817 := S7 394817 (by norm_num) (by norm_num) (by decide) ((by norm_num : 394817 ∣ 1 + 1987 ^ 2).trans hd)
      have g2861 := S1 2861 (by norm_num) (by norm_num) (by decide) 394817 g394817 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2861 g2861 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1987 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1993
    · exfalso; have hd := D1 he
      have g997 := S7 997 (by norm_num) (by norm_num) (by decide) ((by norm_num : 997 ∣ 1 + 1993 ^ 1).trans hd)
      have g499 := S1 499 (by norm_num) (by norm_num) (by decide) 997 g997 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 499 g499 (by norm_num)
    · exfalso; have hd := D2 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1993 ^ 2).trans hd)
    · exfalso; have hd := D4 he
      have g108062830537 := S7 108062830537 prime_108062830537 (by norm_num) (by decide) ((by norm_num : 108062830537 ∣ 1 + 1993 ^ 4).trans hd)
      have g4156262713 := S1 4156262713 prime_4156262713 (by norm_num) (by decide) 108062830537 g108062830537 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 4156262713 g4156262713 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1997
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 1997 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 1997 ^ 2).trans hd)
      have g30677 := S7 30677 (by norm_num) (by norm_num) (by decide) ((by norm_num : 30677 ∣ 1 + 1997 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 30677 g30677 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1997 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1999
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 1999 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g277 := S7 277 (by norm_num) (by norm_num) (by decide) ((by norm_num : 277 ∣ 1 + 1999 ^ 2).trans hd)
      have g139 := S1 139 (by norm_num) (by norm_num) (by decide) 277 g277 (by norm_num)
      have g7213 := S7 7213 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7213 ∣ 1 + 1999 ^ 2).trans hd)
      have g3607 := S1 3607 (by norm_num) (by norm_num) (by decide) 7213 g7213 (by norm_num)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 3607 g3607 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 g139 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g1117793 := S7 1117793 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1117793 ∣ 1 + 1999 ^ 4).trans hd)
      have g186299 := S1 186299 (by norm_num) (by norm_num) (by decide) 1117793 g1117793 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 186299 g186299 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2003
    · exfalso; have hd := D1 he
      have g167 := S7 167 (by norm_num) (by norm_num) (by decide) ((by norm_num : 167 ∣ 1 + 2003 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 2003 ^ 1).trans hd) 167 g167 (by norm_num)
    · exfalso; have hd := D2 he
      have g401201 := S7 401201 (by norm_num) (by norm_num) (by decide) ((by norm_num : 401201 ∣ 1 + 2003 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 401201 g401201 (by norm_num)
    · exfalso; have hd := D4 he
      have g3049 := S7 3049 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3049 ∣ 1 + 2003 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 3049 g3049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2011
    · exfalso; have hd := D1 he
      have g503 := S7 503 (by norm_num) (by norm_num) (by decide) ((by norm_num : 503 ∣ 1 + 2011 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 503 g503 (by norm_num)
    · exfalso; have hd := D2 he
      have g10477 := S7 10477 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10477 ∣ 1 + 2011 ^ 2).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 10477 g10477 (by norm_num)
    · exfalso; have hd := D4 he
      have g8177457331321 := S7 8177457331321 prime_8177457331321 (by norm_num) (by decide) ((by norm_num : 8177457331321 ∣ 1 + 2011 ^ 4).trans hd)
      have g5107 := S1 5107 (by norm_num) (by norm_num) (by decide) 8177457331321 g8177457331321 (by norm_num)
      have g1277 := S1 1277 (by norm_num) (by norm_num) (by decide) 5107 g5107 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1277 g1277 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2017
    · exfalso; have hd := D1 he
      have g1009 := S7 1009 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1009 ∣ 1 + 2017 ^ 1).trans hd)
      have g101 := S1 101 (by norm_num) (by norm_num) (by decide) 1009 g1009 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 101 g101 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 2017 ^ 2).trans hd)
      have g5573 := S7 5573 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5573 ∣ 1 + 2017 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 5573 g5573 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g2386313 := S7 2386313 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2386313 ∣ 1 + 2017 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2386313 g2386313 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2027
    · exfalso; have hd := D1 he
      exact SQ 13 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13 * 13 ∣ 1 + 2027 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2027 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g281 := S7 281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 281 ∣ 1 + 2027 ^ 4).trans hd)
      have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 281 g281 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 281 g281 47 g47 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2029
    · exfalso; have hd := D1 he
      have g29 := S7 29 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29 ∣ 1 + 2029 ^ 1).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 2029 ^ 1).trans hd) 29 g29 (by norm_num)
    · exfalso; have hd := D2 he
      have g55633 := S7 55633 (by norm_num) (by norm_num) (by decide) ((by norm_num : 55633 ∣ 1 + 2029 ^ 2).trans hd)
      have g27817 := S1 27817 (by norm_num) (by norm_num) (by decide) 55633 g55633 (by norm_num)
      have g1987 := S1 1987 (by norm_num) (by norm_num) (by decide) 27817 g27817 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 27817 g27817 1987 g1987 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g94849 := S7 94849 (by norm_num) (by norm_num) (by decide) ((by norm_num : 94849 ∣ 1 + 2029 ^ 4).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 94849 g94849 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2039
    · exfalso; have hd := D1 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2039 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D2 he
      have g2437 := S7 2437 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2437 ∣ 1 + 2039 ^ 2).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 2437 g2437 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D4 he
      have g8642490432721 := S7 8642490432721 prime_8642490432721 (by norm_num) (by decide) ((by norm_num : 8642490432721 ∣ 1 + 2039 ^ 4).trans hd)
      have g116790411253 := S1 116790411253 prime_116790411253 (by norm_num) (by decide) 8642490432721 g8642490432721 (by norm_num)
      have g647 := S1 647 (by norm_num) (by norm_num) (by decide) 116790411253 g116790411253 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 647 g647 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2053
    · simp
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2053 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g216641645201 := S7 216641645201 prime_216641645201 (by norm_num) (by decide) ((by norm_num : 216641645201 ∣ 1 + 2053 ^ 4).trans hd)
      have g1061 := S1 1061 (by norm_num) (by norm_num) (by decide) 216641645201 g216641645201 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1061 g1061 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2063
    · exfalso; have hd := D1 he
      have g43 := S7 43 (by norm_num) (by norm_num) (by decide) ((by norm_num : 43 ∣ 1 + 2063 ^ 1).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 2063 ^ 1).trans hd) 11 g11 (by norm_num)
    · exfalso; have hd := D2 he
      have g5 := S7 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 2063 ^ 2).trans hd)
      have g6977 := S7 6977 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6977 ∣ 1 + 2063 ^ 2).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 6977 g6977 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g13513 := S7 13513 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13513 ∣ 1 + 2063 ^ 4).trans hd)
      have g233 := S1 233 (by norm_num) (by norm_num) (by decide) 13513 g13513 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 233 g233 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2069
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 2069 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g13633 := S7 13633 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13633 ∣ 1 + 2069 ^ 2).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 13633 g13633 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g9162457369561 := S7 9162457369561 prime_9162457369561 (by norm_num) (by decide) ((by norm_num : 9162457369561 ∣ 1 + 2069 ^ 4).trans hd)
      have g34445328457 := S1 34445328457 prime_34445328457 (by norm_num) (by decide) 9162457369561 g9162457369561 (by norm_num)
      have g25799 := S1 25799 (by norm_num) (by norm_num) (by decide) 34445328457 g34445328457 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 25799 g25799 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2081
    · exfalso; have hd := D1 he
      have g347 := S7 347 (by norm_num) (by norm_num) (by decide) ((by norm_num : 347 ∣ 1 + 2081 ^ 1).trans hd)
      exact S8 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 ∣ 1 + 2081 ^ 1).trans hd) 347 g347 (by norm_num)
    · exfalso; have hd := D2 he
      have g89 := S7 89 (by norm_num) (by norm_num) (by decide) ((by norm_num : 89 ∣ 1 + 2081 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
    · exfalso; have hd := D4 he
      have g1289 := S7 1289 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1289 ∣ 1 + 2081 ^ 4).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 1289 g1289 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1289 g1289 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2083
    · exfalso; have hd := D1 he
      have g521 := S7 521 (by norm_num) (by norm_num) (by decide) ((by norm_num : 521 ∣ 1 + 2083 ^ 1).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 521 g521 (by norm_num)
    · exfalso; have hd := D2 he
      have g433889 := S7 433889 (by norm_num) (by norm_num) (by decide) ((by norm_num : 433889 ∣ 1 + 2083 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 433889 g433889 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2083 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2087
    · exfalso; have hd := D1 he
      exact SQ 3 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3 * 3 ∣ 1 + 2087 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2087 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D4 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 2087 ^ 4).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2089
    · exfalso; have hd := D1 he
      have g19 := S7 19 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19 ∣ 1 + 2089 ^ 1).trans hd)
      exact S8 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 ∣ 1 + 2089 ^ 1).trans hd) 19 g19 (by norm_num)
    · exfalso; have hd := D2 he
      have g3301 := S7 3301 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3301 ∣ 1 + 2089 ^ 2).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 3301 g3301 (by norm_num)
      have g661 := S7 661 (by norm_num) (by norm_num) (by decide) ((by norm_num : 661 ∣ 1 + 2089 ^ 2).trans hd)
      have g331 := S1 331 (by norm_num) (by norm_num) (by decide) 661 g661 (by norm_num)
      have g83 := S1 83 (by norm_num) (by norm_num) (by decide) 331 g331 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 13 g13 83 g83 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2089 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2099
    · exfalso; have hd := D1 he
      exact SQ 5 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5 * 5 ∣ 1 + 2099 ^ 1).trans hd)
    · exfalso; have hd := D2 he
      have g1709 := S7 1709 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1709 ∣ 1 + 2099 ^ 2).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1709 g1709 (by norm_num)
    · exfalso; have hd := D4 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2099 ^ 4).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

-- The sieve of z.
theorem zsieve {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 7 ≤ z) (hi : z < 2100)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 2 = 1 → z ∈ ({7, 11, 13, 19, 23, 31, 37, 41, 43, 47, 61, 73, 79, 83, 103, 127, 139, 151, 157, 163, 167,
      191, 223, 277, 307, 311, 313, 331, 367, 383, 433, 487, 571, 601, 607, 613, 617, 619, 631,
      643, 661, 733, 743, 751, 761, 823, 853, 991, 1039, 1063, 1117, 1201, 1213, 1231, 1237,
      1279, 1301, 1303, 1321, 1327, 1471, 1487, 1523, 1531, 1663, 1777, 1783, 1951, 2053} : Finset ℕ)) ∧
    (e % 4 = 2 → z ∈ ({11, 139, 181, 199, 271} : Finset ℕ)) ∧
    (e % 8 = 4 → z ∈ ({7, 11, 419, 463, 503, 607, 883, 1019, 1327} : Finset ℕ)) := by
  rcases Nat.lt_or_ge z 300 with h | h
  · exact zs_0 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 600 with h | h
  · exact zs_300 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 900 with h | h
  · exact zs_600 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1200 with h | h
  · exact zs_900 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1500 with h | h
  · exact zs_1200 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1800 with h | h
  · exact zs_1500 hP hz (by omega) h E
  exact zs_1800 hP hz (by omega) hi E

-- Section 3. The step.
theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.H4 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max A1 (max A2 (max A3 A4)),
    fun n h z hz lo hi hS _ h7 c0 c1 c2 _ c4 c5 c6 c7 c15 R => ?_⟩
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := by omega
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have U : Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1) :=
    fun ha d hd => odd_two_divisor hP hz lo E (Nat.odd_iff.mp ha) hd
  obtain ⟨z1, z2, z4⟩ := zsieve hP hz lo hi E
  have hc : n.factorization z % 2 = 1 ∨ n.factorization z % 4 = 2 ∨ n.factorization z % 8 = 4 ∨ n.factorization z % 8 = 0 := by omega
  rcases hc with c | c | c | c
  · exact (h1 n h z hz hS (Nat.odd_iff.mpr c) (z1 c)
      (fun hz3 d hd => odd_divisor_mod_six hP hz hz3 hz2 E (odd_of_dvd_odd hd c)
        (one_add_pow_dvd_of_odd_mul (mod_of_dvd_odd hd c)))
      (fun hz3 => Nat.even_iff.mpr (by
        by_contra hne
        exact not_odd_odd hP hz hz3 E (by omega) c))
      h7 c0 c1 c2 c4 c5 c6 c7 c15 U R).trans (le_max_left _ _)
  · exact (h2 n h z hz hS c (z2 c) c0 c1 c2 c4 c5 c6 c7 c15 U R).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · have hm := z4 c
    have hz7 : z ≠ 7 := by
      rintro rfl
      exact (h7 rfl).2 4 (by simp) c
    rw [Finset.mem_insert] at hm
    exact (h3 n h z hz hS c (hm.resolve_left hz7) c0 c1 c2 c4 c5 c6 c7 c15 U R).trans
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  · exact (h4 n h z hz lo hi hS c h7 c0 c1 c2 c4 c5 c6 c7 c15 U R).trans
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1
