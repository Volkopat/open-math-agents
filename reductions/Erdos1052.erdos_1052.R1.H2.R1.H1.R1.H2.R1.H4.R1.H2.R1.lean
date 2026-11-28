import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1

/-!
# Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H2.R1

Credit: @sanchan (building on @aroth01's desk notes #90767 and #94530).

Eliminates `z ∈ {139, 199, 271}` unconditionally via forced chains from `1 + z^2 ∣ 1 + z^e`,
eliminates `z = 181` completely for all `a ≥ 20` (including `a ≡ 2 mod 4`) via Graham weights,
eliminates `z = 11` for `a` odd and `4 ∣ a` (all `a ≥ 20`), and for the remaining case `z = 11`,
`a ≡ 2 mod 4` forces `7 ∣ n` and `¬ 13 ∣ n`, splitting into `H1` (`e = 2`) and `H2`
(`6 ≤ e`, `e ≡ 2 mod 4`).
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1 hiding H1 H2 H3 H4 main

-- H1: z = 11, e = 2, a = 2 mod 4 (with 7 | n and ¬ 13 | n).
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 11) →
    n.factorization 11 = 2 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n % 20 ≠ 10 →
    padicValNat 2 n % 28 ≠ 14 →
    7 ∣ n → ¬ 13 ∣ n →
    padicValNat 2 n ≤ A

-- H2: z = 11, 6 <= e with e = 2 mod 4, a = 2 mod 4 (with 7 | n and ¬ 13 | n).
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 11) →
    6 ≤ n.factorization 11 →
    n.factorization 11 % 4 = 2 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n % 20 ≠ 10 →
    padicValNat 2 n % 28 ≠ 14 →
    7 ∣ n → ¬ 13 ∣ n →
    padicValNat 2 n ≤ A

-- Section 1. Elementary helpers (chain contradictions and 4 | a prime lower bound).

theorem two_pow_mod_three_even {m : ℕ} (hm : m % 2 = 0) : (2 ^ m + 1) % 3 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  rw [pow_mul]
  have h4 : ∀ t : ℕ, (2 ^ 2) ^ t % 3 = 1 := fun t => by
    induction t with
    | zero => norm_num
    | succ t ih => rw [pow_succ, Nat.mul_mod, ih]; norm_num
  have := h4 k
  omega

theorem not_dvd_two_pow_four_mul {p m k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Odd m) (h16 : 16 ^ m % p = 1) : ¬ p ∣ 2 ^ (4 * k) + 1 := by
  intro hd
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((2 ^ (4 * k) + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  have h16k : (16 : ZMod p) ^ k = -1 := by
    push_cast at h1
    have hpow : (2 : ZMod p) ^ (4 * k) = (16 : ZMod p) ^ k := by
      rw [pow_mul]
      norm_num
    rw [hpow] at h1
    linear_combination h1
  have h16m : (16 : ZMod p) ^ m = 1 := by
    have hmod : (16 ^ m : ℕ) ≡ 1 [MOD p] := by
      rw [Nat.ModEq, h16, Nat.mod_eq_of_lt hp.one_lt]
    have := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hmod
    push_cast at this
    exact this
  have hneg : (-1 : ZMod p) ^ m = 1 := by
    rw [← h16k, ← pow_mul, mul_comm, pow_mul, h16m, one_pow]
  rw [hm.neg_one_pow] at hneg
  have h2z : (2 : ZMod p) = 0 := by linear_combination -hneg
  have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2z)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2d)

theorem exists_p0_ge_41 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime) (hz3 : z ≠ 3) (hm0 : m ≠ 0)
    (hz_ne : ∀ p : ℕ, p.Prime → p ∣ 2 ^ m + 1 → p % 3 = 2 → p ≠ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hm4 : m % 4 = 0) :
    ∃ p0 ∈ P, p0 ∣ 2 ^ m + 1 ∧ p0 % 3 = 2 ∧ 41 ≤ p0 := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k := ⟨m / 4, by omega⟩
  obtain ⟨p0, hp0p, hp0d, hp03⟩ := exists_prime_mod3 (2 ^ (4 * k) + 1) (two_pow_mod_three_even (by omega))
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ (4 * k) := dvd_pow_self 2 hm0
    have : 2 ∣ 1 := (Nat.dvd_add_right this).mp hp0d
    omega
  have hp0z : p0 ≠ z := hz_ne p0 hp0p hp0d hp03
  have hp0P : p0 ∈ P := S2 p0 hp0p hp02 (hnz hp0z) hp0d
  refine ⟨p0, hp0P, hp0d, hp03, ?_⟩
  by_contra hlt
  push Not at hlt
  have h5 : p0 ≠ 5 := fun h => not_dvd_two_pow_four_mul (k := k) (p := 5) (m := 1)
    (by norm_num) (by norm_num) ⟨0, by norm_num⟩ (by norm_num) (h ▸ hp0d)
  have h11 : p0 ≠ 11 := fun h => not_dvd_two_pow_four_mul (k := k) (p := 11) (m := 5)
    (by norm_num) (by norm_num) ⟨2, by norm_num⟩ (by norm_num) (h ▸ hp0d)
  have h17 : p0 ≠ 17 := by
    rintro rfl
    exact S6 3 Nat.prime_three (by norm_num) (hnz hz3.symm) 17 hp0P (by norm_num)
  have h23 : p0 ≠ 23 := fun h => not_dvd_two_pow_four_mul (k := k) (p := 23) (m := 11)
    (by norm_num) (by norm_num) ⟨5, by norm_num⟩ (by norm_num) (h ▸ hp0d)
  have h29 : p0 ≠ 29 := fun h => not_dvd_two_pow_four_mul (k := k) (p := 29) (m := 7)
    (by norm_num) (by norm_num) ⟨3, by norm_num⟩ (by norm_num) (h ▸ hp0d)
  interval_cases p0 <;>
    first | exact h5 rfl | exact h11 rfl | exact h17 rfl | exact h23 rfl | exact h29 rfl
          | omega | norm_num at hp0p

-- Contradiction whenever a prime q in P with 3 | q + 1 is already consumed by some p in P,
-- provided z % 3 = 1 (so 3 != z and no prime c = 2 mod 3 equals z) and m != 0.
theorem kill_consumed_mod3 {m e z q p : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, x.Prime ∧ x ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 1) (hm0 : m ≠ 0)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ x ∈ P, (x + 1) = 2 ^ (m + 1) * z ^ e * ∏ x ∈ P, x)
    (hqP : q ∈ P) (hpP : p ∈ P) (hq3 : 3 ∣ q + 1) (hqp : q ∣ p + 1) : False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, S4, -, -, -, -⟩ := facts hP hK E
  rcases Nat.even_or_odd m with hm | hm
  · have hm2 : m % 2 = 0 := Nat.even_iff.mp hm
    obtain ⟨c, hcp, hcd, hc3⟩ := exists_prime_mod3 (2 ^ m + 1) (two_pow_mod_three_even hm2)
    have hc2 : c ≠ 2 := by
      rintro rfl
      have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 hm0
      have h21 : 2 ∣ 1 := (Nat.dvd_add_right h2m).mp hcd
      omega
    have hcz : c ≠ z := by omega
    have hcP : c ∈ P := S2 c hcp hc2 (hnz hcz) hcd
    have hcq : c = q := S3 3 Nat.prime_three (by norm_num) (hnz (by omega)) c hcP q hqP (by omega) hq3
    exact S4 c hcp hc2 (hnz hcz) hcd p hpP (hcq ▸ hqp)
  · have h3m : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one (Nat.odd_iff.mp hm)
    exact S4 3 Nat.prime_three (by norm_num) (hnz (by omega)) h3m q hqP hq3

theorem kill_z139 {m e : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, x.Prime ∧ x ≠ 2) (hm0 : m ≠ 0)
    (E : (2 ^ m + 1) * (1 + 139 ^ e) * ∏ x ∈ P, (x + 1) = 2 ^ (m + 1) * 139 ^ e * ∏ x ∈ P, x)
    (he : e % 4 = 2) : False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 139) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 139 → c ∉ ({139} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, -, -, -, -, S7, -⟩ := facts hP hK E
  have hd : 1 + 139 ^ 2 ∣ 1 + 139 ^ e := one_add_pow_dvd_of_odd_mul (z := 139) (e0 := 2) he
  have h9661 : 9661 ∈ P := S7 9661 (by norm_num) (by norm_num) (hnz (by norm_num))
    (Dvd.dvd.trans (by norm_num) hd)
  have h4831 : 4831 ∈ P := S1 4831 (by norm_num) (by norm_num) (hnz (by norm_num)) 9661 h9661 (by norm_num)
  have h151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 4831 h4831 (by norm_num)
  have h19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 h151 (by norm_num)
  have h5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 h19 (by norm_num)
  exact kill_consumed_mod3 hP (by norm_num) (by norm_num) hm0 E h5 h19 (by norm_num) (by norm_num)

theorem kill_z199 {m e : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, x.Prime ∧ x ≠ 2) (hm0 : m ≠ 0)
    (E : (2 ^ m + 1) * (1 + 199 ^ e) * ∏ x ∈ P, (x + 1) = 2 ^ (m + 1) * 199 ^ e * ∏ x ∈ P, x)
    (he : e % 4 = 2) : False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 199) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 199 → c ∉ ({199} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, -, -, -, -, S7, -⟩ := facts hP hK E
  have hd : 1 + 199 ^ 2 ∣ 1 + 199 ^ e := one_add_pow_dvd_of_odd_mul (z := 199) (e0 := 2) he
  have h19801 : 19801 ∈ P := S7 19801 (by norm_num) (by norm_num) (hnz (by norm_num))
    (Dvd.dvd.trans (by norm_num) hd)
  have h9901 : 9901 ∈ P := S1 9901 (by norm_num) (by norm_num) (hnz (by norm_num)) 19801 h19801 (by norm_num)
  have h4951 : 4951 ∈ P := S1 4951 (by norm_num) (by norm_num) (hnz (by norm_num)) 9901 h9901 (by norm_num)
  have h619 : 619 ∈ P := S1 619 (by norm_num) (by norm_num) (hnz (by norm_num)) 4951 h4951 (by norm_num)
  have h5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 619 h619 (by norm_num)
  exact kill_consumed_mod3 hP (by norm_num) (by norm_num) hm0 E h5 h619 (by norm_num) (by norm_num)

theorem kill_z271 {m e : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, x.Prime ∧ x ≠ 2) (hm0 : m ≠ 0)
    (E : (2 ^ m + 1) * (1 + 271 ^ e) * ∏ x ∈ P, (x + 1) = 2 ^ (m + 1) * 271 ^ e * ∏ x ∈ P, x)
    (he : e % 4 = 2) : False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 271) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 271 → c ∉ ({271} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, -, -, -, -, S7, -⟩ := facts hP hK E
  have hd : 1 + 271 ^ 2 ∣ 1 + 271 ^ e := one_add_pow_dvd_of_odd_mul (z := 271) (e0 := 2) he
  have h36721 : 36721 ∈ P := S7 36721 (by norm_num) (by norm_num) (hnz (by norm_num))
    (Dvd.dvd.trans (by norm_num) hd)
  have h43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 36721 h36721 (by norm_num)
  have h11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 h43 (by norm_num)
  exact kill_consumed_mod3 hP (by norm_num) (by norm_num) hm0 E h11 h43 (by norm_num) (by norm_num)

-- Section 2. Leaf bounds and small-parent exclusions for Graham weights.

theorem two_mul_dvd_of_odd {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : c % 2 = 1)
    (hd : c ∣ p + 1) : 2 * c ∣ p + 1 := by
  have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h2 : 2 ∣ p + 1 := by omega
  have hcop : Nat.Coprime 2 c := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hc
  exact hcop.mul_dvd_of_dvd_of_dvd h2 hd

theorem parent_ge_of_c7 {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpz : p ≠ z) (hp13 : p ≠ 13)
    (hz3 : z ≠ 3) (hz5 : z ≠ 5) (_hz7 : z ≠ 7)
    (h7 : 7 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 7 ≤ c')
    (hsq7 : ¬ 7 * 7 ∣ p + 1) :
    (z = 181 → 223 ≤ p) ∧ (z = 11 → 181 ≤ p) := by
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h7
  have h3m : k % 3 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 3 (by norm_num) (by norm_num) (hnz hz3.symm) ⟨14 * t, by omega⟩
    omega
  have h5m : k % 5 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 5 (by norm_num) (by norm_num) (hnz hz5.symm) ⟨14 * t, by omega⟩
    omega
  have h7m : k % 7 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    exact hsq7 ⟨2 * t, by omega⟩
  constructor
  · intro hz181
    by_contra hlt
    have hk15 : 1 ≤ k ∧ k ≤ 15 := by omega
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 11 ∨ k = 13 := by omega
    rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp13 (by omega)
    · norm_num [show p = 27 from by omega] at hp
    · norm_num [show p = 55 from by omega] at hp
    · norm_num [show p = 111 from by omega] at hp
    · norm_num [show p = 153 from by omega] at hp
    · exact hpz (by omega)
  · intro hz11
    by_contra hlt
    have hk12 : 1 ≤ k ∧ k ≤ 12 := by omega
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 11 := by omega
    rcases hk_cases with rfl | rfl | rfl | rfl | rfl
    · exact hp13 (by omega)
    · norm_num [show p = 27 from by omega] at hp
    · norm_num [show p = 55 from by omega] at hp
    · norm_num [show p = 111 from by omega] at hp
    · norm_num [show p = 153 from by omega] at hp

theorem parent_ge_103_of_c13_z11 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h13 : 13 ∣ p + 1) :
    103 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h13
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 25 from by omega] at hp
  · norm_num [show p = 51 from by omega] at hp
  · norm_num [show p = 77 from by omega] at hp

theorem parent_ge_487_of_c31_z181 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp61 : p ≠ 61)
    (h31 : 31 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({181} : Finset ℕ) → c' ∣ p + 1 → 31 ≤ c') :
    487 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h31
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk7 : k ≤ 7 := by omega
  interval_cases k
  · exact hp61 (by omega)
  · norm_num [show p = 123 from by omega] at hp
  · norm_num [show p = 185 from by omega] at hp
  · norm_num [show p = 247 from by omega] at hp
  · norm_num [show p = 309 from by omega] at hp
  · norm_num [show p = 371 from by omega] at hp
  · have := hmin 7 (by norm_num) (by norm_num) (by decide) ⟨62, by omega⟩
    omega

theorem parent_ge_487_of_c61_z181 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h61 : 61 ∣ p + 1) :
    487 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h61
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 121 from by omega] at hp
  · norm_num [show p = 243 from by omega] at hp
  · norm_num [show p = 365 from by omega] at hp

theorem parent_ge_823_of_c103_z181 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h103 : 103 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({181} : Finset ℕ) → c' ∣ p + 1 → 103 ≤ c') :
    823 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h103
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 205 from by omega] at hp
  · norm_num [show p = 411 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (by decide) ⟨206, by omega⟩
    omega

theorem parent_ge_1000_of_c127_z181 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h127 : 127 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({181} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    1000 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h127
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 253 from by omega] at hp
  · norm_num [show p = 507 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (by decide) ⟨254, by omega⟩
    omega

theorem parent_ge_1000_of_c13_z181 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp103 : p ≠ 103) (hp883 : p ≠ 883) (_hp181 : p ≠ 181)
    (h13 : 13 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({181} : Finset ℕ) → c' ∣ p + 1 → 13 ≤ c')
    (hsq13 : ¬ 13 * 13 ∣ p + 1) :
    1000 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h13
  have h3m : k % 3 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 3 (by norm_num) (by norm_num) (by decide) ⟨26 * t, by omega⟩
    omega
  have h5m : k % 5 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 5 (by norm_num) (by norm_num) (by decide) ⟨26 * t, by omega⟩
    omega
  have h7m : k % 7 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 7 (by norm_num) (by norm_num) (by decide) ⟨26 * t, by omega⟩
    omega
  have h11m : k % 11 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 11 (by norm_num) (by norm_num) (by decide) ⟨26 * t, by omega⟩
    omega
  have h13m : k % 13 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    exact hsq13 ⟨2 * t, by omega⟩
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk38 : k ≤ 38 := by omega
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 17 ∨ k = 19 ∨
      k = 23 ∨ k = 29 ∨ k = 31 ∨ k = 32 ∨ k = 34 ∨ k = 37 ∨ k = 38 := by
    interval_cases k <;> omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [show p = 25 from by omega] at hp
  · norm_num [show p = 51 from by omega] at hp
  · exact hp103 (by omega)
  · norm_num [show p = 207 from by omega] at hp
  · norm_num [show p = 415 from by omega] at hp
  · norm_num [show p = 441 from by omega] at hp
  · norm_num [show p = 493 from by omega] at hp
  · norm_num [show p = 597 from by omega] at hp
  · norm_num [show p = 753 from by omega] at hp
  · norm_num [show p = 805 from by omega] at hp
  · norm_num [show p = 831 from by omega] at hp
  · exact hp883 (by omega)
  · norm_num [show p = 961 from by omega] at hp
  · norm_num [show p = 987 from by omega] at hp

-- Bound on the product of beta over 181-leaves in L.
theorem leaf181_bound {L : Finset ℕ} {β : ℕ → ℚ}
    (hLp : ∀ q ∈ L, q.Prime ∧ q ≠ 2)
    (hL181 : ∀ q ∈ L, 181 ∣ q + 1 ∧ ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 181)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1)) :
    ∏ q ∈ L, β q ≤ (1448 / 1446) * (2896 / 2894) * ((181 : ℚ) ^ 2 / ((181 : ℚ) ^ 2 - 3)) := by
  have hB : ∏ q ∈ L, β q ≤ ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
    Finset.prod_le_prod (fun q hq => (hLβ q hq).1.le) (fun q hq => (hLβ q hq).2)
  refine hB.trans ?_
  rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => ¬ 181 ^ 2 ∣ q + 1)]
  have hkj : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 181 ^ j := fun q hq => by
    obtain ⟨k, j, heq⟩ := two_pow_mul_pow_of_odd_primes_eq (by omega) (hL181 q hq).2
    have hodd := Nat.odd_iff.mp ((hLp q hq).1.odd_of_ne_two (hLp q hq).2)
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero, one_mul] at heq
      have : ∀ t : ℕ, (181 ^ t) % 2 = 1 := fun t => by
        induction t with
        | zero => norm_num
        | succ t ih => rw [pow_succ, Nat.mul_mod, ih]
      have := this j
      omega
    have hj1 : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      rw [hj0, pow_zero, mul_one] at heq
      have h181d : 181 ∣ 2 ^ k := heq ▸ (hL181 q hq).1
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow (by norm_num) h181d)
      norm_num at this
    exact ⟨k, j, hk1, hj1, heq⟩
  have hpart2 : ∏ q ∈ L.filter (fun q => ¬ ¬ 181 ^ 2 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ (181 : ℚ) ^ 2 / ((181 : ℚ) ^ 2 - 3) := by
    refine zleaf_bound (z := 181) (by norm_num) 2 (by norm_num) _ (fun q hq => ?_)
    obtain ⟨hqL, hdiv⟩ := Finset.mem_filter.mp hq
    push Not at hdiv
    obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
    refine ⟨k, j, hk1, ?_, heq⟩
    by_contra hjlt
    have hj : j = 1 := by omega
    rw [heq, hj, pow_one] at hdiv
    have h181' : 181 ∣ 2 ^ k := by
      have : 181 * 181 ∣ 2 ^ k * 181 := by simpa [sq] using hdiv
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h181')
    norm_num at this
  have hpart1 : ∏ q ∈ L.filter (fun q => ¬ 181 ^ 2 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ (1448 / 1446) * (2896 / 2894) := by
    rw [← Finset.prod_filter_mul_prod_filter_not _ (fun q => q = 1447)]
    have h1447 : ∏ q ∈ (L.filter (fun q => ¬ 181 ^ 2 ∣ q + 1)).filter (fun q => q = 1447),
        (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 1448 / 1446 := by
      have hsub : (L.filter (fun q => ¬ 181 ^ 2 ∣ q + 1)).filter (fun q => q = 1447) ⊆ {1447} := by
        intro q hq
        exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hq).2
      have h := Finset.prod_le_prod_of_subset_of_one_le (f := fun q : ℕ => ((q : ℚ) + 1) / ((q : ℚ) - 1))
        hsub (fun q hq => by
          have : q = 1447 := (Finset.mem_filter.mp hq).2
          subst this; norm_num)
        (fun q hq _ => by
          rw [Finset.mem_singleton.mp hq]; norm_num)
      rw [Finset.prod_singleton] at h
      exact h.trans (by norm_num)
    have hgt : ∏ q ∈ (L.filter (fun q => ¬ 181 ^ 2 ∣ q + 1)).filter (fun q => ¬ q = 1447),
        (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2896 / 2894 := by
      have hf := fiber_bound (u := 2896) (by norm_num)
        ((L.filter (fun q => ¬ 181 ^ 2 ∣ q + 1)).filter (fun q => ¬ q = 1447)) (fun q hq => by
          obtain ⟨hq1, hne⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqL, hndiv⟩ := Finset.mem_filter.mp hq1
          obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
          have hj : j = 1 := by
            by_contra hne1
            have hj2 : 2 ≤ j := by omega
            apply hndiv
            rw [heq]
            exact dvd_mul_of_dvd_right (pow_dvd_pow 181 hj2) _
          rw [hj, pow_one] at heq
          have hk5 : 5 ≤ k := by
            by_contra hklt
            have hkp := (hLp q hqL).1
            interval_cases k
            · norm_num [show q = 361 from by omega] at hkp
            · norm_num [show q = 723 from by omega] at hkp
            · exact hne (by omega)
            · norm_num [show q = 2895 from by omega] at hkp
          refine ⟨k - 4, by omega, ?_⟩
          have hk_eq : (k - 4) + 4 = k := by omega
          have heq' : q + 1 = 2 ^ ((k - 4) + 4) * 181 := by rwa [hk_eq]
          rw [heq', pow_add]
          ring)
      exact hf.trans (by norm_num)
    exact mul_le_mul h1447 hgt
      (Finset.prod_nonneg fun q hq => B_nonneg ((hLp q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.one_le))
      (by norm_num)
  exact mul_le_mul hpart1 hpart2
    (Finset.prod_nonneg fun q hq => B_nonneg ((hLp q (Finset.mem_filter.mp hq).1).1.one_le))
    (by norm_num)

-- Bound on the product of beta over 11-leaves in L.
theorem leaf11_bound {L : Finset ℕ} {β : ℕ → ℚ}
    (hLp : ∀ q ∈ L, q.Prime ∧ q ≠ 2)
    (hL11 : ∀ q ∈ L, 11 ∣ q + 1 ∧ ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 11)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1)) :
    ∏ q ∈ L, β q ≤ (44 / 42) * (704 / 702) * ((11 : ℚ) ^ 2 / ((11 : ℚ) ^ 2 - 3)) := by
  have hB : ∏ q ∈ L, β q ≤ ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
    Finset.prod_le_prod (fun q hq => (hLβ q hq).1.le) (fun q hq => (hLβ q hq).2)
  refine hB.trans ?_
  rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => ¬ 11 ^ 2 ∣ q + 1)]
  have hkj : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 11 ^ j := fun q hq => by
    obtain ⟨k, j, heq⟩ := two_pow_mul_pow_of_odd_primes_eq (by omega) (hL11 q hq).2
    have hodd := Nat.odd_iff.mp ((hLp q hq).1.odd_of_ne_two (hLp q hq).2)
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero, one_mul] at heq
      have : ∀ t : ℕ, (11 ^ t) % 2 = 1 := fun t => by
        induction t with
        | zero => norm_num
        | succ t ih => rw [pow_succ, Nat.mul_mod, ih]
      have := this j
      omega
    have hj1 : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      rw [hj0, pow_zero, mul_one] at heq
      have h11d : 11 ∣ 2 ^ k := heq ▸ (hL11 q hq).1
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow (by norm_num) h11d)
      norm_num at this
    exact ⟨k, j, hk1, hj1, heq⟩
  have hpart2 : ∏ q ∈ L.filter (fun q => ¬ ¬ 11 ^ 2 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ (11 : ℚ) ^ 2 / ((11 : ℚ) ^ 2 - 3) := by
    refine zleaf_bound (z := 11) (by norm_num) 2 (by norm_num) _ (fun q hq => ?_)
    obtain ⟨hqL, hdiv⟩ := Finset.mem_filter.mp hq
    push Not at hdiv
    obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
    refine ⟨k, j, hk1, ?_, heq⟩
    by_contra hjlt
    have hj : j = 1 := by omega
    rw [heq, hj, pow_one] at hdiv
    have h11' : 11 ∣ 2 ^ k := by
      have : 11 * 11 ∣ 2 ^ k * 11 := by simpa [sq] using hdiv
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h11')
    norm_num at this
  have hpart1 : ∏ q ∈ L.filter (fun q => ¬ 11 ^ 2 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ (44 / 42) * (704 / 702) := by
    rw [← Finset.prod_filter_mul_prod_filter_not _ (fun q => q = 43)]
    have h43 : ∏ q ∈ (L.filter (fun q => ¬ 11 ^ 2 ∣ q + 1)).filter (fun q => q = 43),
        (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 44 / 42 := by
      have hsub : (L.filter (fun q => ¬ 11 ^ 2 ∣ q + 1)).filter (fun q => q = 43) ⊆ {43} := by
        intro q hq
        exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hq).2
      have h := Finset.prod_le_prod_of_subset_of_one_le (f := fun q : ℕ => ((q : ℚ) + 1) / ((q : ℚ) - 1))
        hsub (fun q hq => by
          have : q = 43 := (Finset.mem_filter.mp hq).2
          subst this; norm_num)
        (fun q hq _ => by
          rw [Finset.mem_singleton.mp hq]; norm_num)
      rw [Finset.prod_singleton] at h
      exact h.trans (by norm_num)
    have hgt : ∏ q ∈ (L.filter (fun q => ¬ 11 ^ 2 ∣ q + 1)).filter (fun q => ¬ q = 43),
        (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 704 / 702 := by
      have hf := fiber_bound (u := 704) (by norm_num)
        ((L.filter (fun q => ¬ 11 ^ 2 ∣ q + 1)).filter (fun q => ¬ q = 43)) (fun q hq => by
          obtain ⟨hq1, hne⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqL, hndiv⟩ := Finset.mem_filter.mp hq1
          obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
          have hj : j = 1 := by
            by_contra hne1
            have hj2 : 2 ≤ j := by omega
            apply hndiv
            rw [heq]
            exact dvd_mul_of_dvd_right (pow_dvd_pow 11 hj2) _
          rw [hj, pow_one] at heq
          have hk7 : 7 ≤ k := by
            by_contra hklt
            have hkp := (hLp q hqL).1
            interval_cases k
            · norm_num [show q = 21 from by omega] at hkp
            · exact hne (by omega)
            · norm_num [show q = 87 from by omega] at hkp
            · norm_num [show q = 175 from by omega] at hkp
            · norm_num [show q = 351 from by omega] at hkp
            · norm_num [show q = 703 from by omega] at hkp
          refine ⟨k - 6, by omega, ?_⟩
          have hk_eq : (k - 6) + 6 = k := by omega
          have heq' : q + 1 = 2 ^ ((k - 6) + 6) * 11 := by rwa [hk_eq]
          rw [heq', pow_add]
          ring)
      exact hf.trans (by norm_num)
    exact mul_le_mul h43 hgt
      (Finset.prod_nonneg fun q hq => B_nonneg ((hLp q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.one_le))
      (by norm_num)
  exact mul_le_mul hpart1 hpart2
    (Finset.prod_nonneg fun q hq => B_nonneg ((hLp q (Finset.mem_filter.mp hq).1).1.one_le))
    (by norm_num)

-- Combined wrapper: applies master_gen + mersenne_bound + z-leaf bound for z in {11, 181}.
theorem graham_contra {m e z : ℕ} {P : Finset ℕ} {zB : ℚ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hm : 20 ≤ m) (he : 2 ≤ e)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hzL : ∀ L : Finset ℕ, (∀ q ∈ L, q.Prime ∧ q ≠ 2) →
        (∀ q ∈ L, z ∣ q + 1 ∧ ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = z) →
        (∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1)) → ∏ q ∈ L, β q ≤ zB)
    (hnum : (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ 2) *
        ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047) * zB) < 2) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hK0 : 0 < z ^ e := pow_pos hz.pos e
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK hK0 E β hB h4
  have hLpos : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
    have hb := hB q (hLP hq)
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    exact ⟨by linarith [hb.1], hb.2⟩
  rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => ¬ z ∣ q + 1)] at hmain
  have hM : ∏ q ∈ L.filter (fun q => ¬ z ∣ q + 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => two_pow_of_no_odd_prime (fun c hc hc2 hcd => by
        obtain ⟨hqL, hnd⟩ := Finset.mem_filter.mp hq
        have hcz : c = z := Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd)
        exact hnd (hcz ▸ hcd)))
      (fun q hq => hLpos q (Finset.mem_filter.mp hq).1) h1
  have hZ : ∏ q ∈ L.filter (fun q => ¬ ¬ z ∣ q + 1), β q ≤ zB := by
    refine hzL _ (fun q hq => hP q (hLP (Finset.mem_filter.mp hq).1))
      (fun q hq => by
        obtain ⟨hqL, hd⟩ := Finset.mem_filter.mp hq
        push Not at hd
        exact ⟨hd, fun c hc hc2 hcd => Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd)⟩)
      (fun q hq => hLpos q (Finset.mem_filter.mp hq).1)
  have hprod : (∏ q ∈ L.filter (fun q => ¬ z ∣ q + 1), β q) *
      (∏ q ∈ L.filter (fun q => ¬ ¬ z ∣ q + 1), β q) ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) * zB :=
    mul_le_mul hM hZ (Finset.prod_nonneg fun q hq => (hLpos q (Finset.mem_filter.mp hq).1).1.le)
      (by have := h1.1; have := h1.2.1; have := h1.2.2.1; have := h1.2.2.2; positivity)
  have h2m : (1 + 1 / (2 : ℚ) ^ m) ≤ 1 + 1 / (2 : ℚ) ^ 20 := by
    have hpow : (2 : ℚ) ^ 20 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have := one_div_le_one_div_of_le (by positivity : (0 : ℚ) < (2 : ℚ) ^ 20) hpow
    linarith
  have hze : ((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ) ≤ 1 + 1 / (z : ℚ) ^ 2 := by
    have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hz.one_le
    have hpow : (z : ℚ) ^ 2 ≤ (z : ℚ) ^ e := pow_le_pow_right₀ hz1 he
    have hpos : (0 : ℚ) < (z : ℚ) ^ 2 := by positivity
    have hpos2 : (0 : ℚ) < (z : ℚ) ^ e := by positivity
    have hdiv := one_div_le_one_div_of_le hpos hpow
    push_cast
    rw [add_div, div_self hpos2.ne']
    linarith
  have hfac : (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) ≤
      (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ 2) :=
    mul_le_mul h2m hze (by positivity) (by positivity)
  have htot := mul_le_mul hfac hprod
    (mul_nonneg (Finset.prod_nonneg fun q hq => (hLpos q (Finset.mem_filter.mp hq).1).1.le)
      (Finset.prod_nonneg fun q hq => (hLpos q (Finset.mem_filter.mp hq).1).1.le))
    (by positivity)
  linarith

-- Section 3. Complete elimination of z = 181 for all m >= 20.

theorem kill_z181 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h181P : 181 ∉ P) (hm : 20 ≤ m) (he : e % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 181 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 181 ^ e * ∏ p ∈ P, p) :
    False := by
  have he2 : 2 ≤ e := by omega
  have hK := prime_dvd_prime_pow (e := e) (z := 181) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 181 → c ∉ ({181} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, S6, -, -⟩ := facts hP hK E
  have hmod4 : m % 2 = 1 ∨ m % 4 = 0 ∨ m % 4 = 2 := by omega
  rcases hmod4 with hodd | hm4 | hm2
  · -- Subcase 181.a: m odd -> 3 | 2^m + 1, so beta 3 = 4/3.
    let β : ℕ → ℚ := fun p => if p = 3 then 4 / 3 else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    have h3m : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one hodd
    refine graham_contra (z := 181) (zB := (1448 / 1446) * (2896 / 2894) * ((181 : ℚ) ^ 2 / ((181 : ℚ) ^ 2 - 3)))
      hP (by norm_num) hm he2 E β ?_ ?_ ?_ (fun L hLp hL181 hLβ => leaf181_bound hLp hL181 hLβ) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3
      · subst h3; norm_num
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c _ hcd _ hne
      dsimp only [β] at hne
      split_ifs at hne with h3
      · subst h3
        exact absurd hcd (S4 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) h3m p hp)
      · exact absurd rfl hne
    · dsimp only [β]; norm_num
    · dsimp only [β]; norm_num
  · -- Subcase 181.b: 4 | m -> exists p0 in P, p0 | 2^m + 1, p0 = 2 mod 3, p0 >= 41.
    obtain ⟨p0, hp0P, hp0d, hp03, hp041⟩ := exists_p0_ge_41 hP (z := 181) (by norm_num) (by norm_num) (by omega)
      (fun _ _ _ h3 heq => by omega) E hm4
    have hp0p : p0.Prime := (hP p0 hp0P).1
    have hp02 : p0 ≠ 2 := (hP p0 hp0P).2
    have hne3 : p0 ≠ 3 := by omega
    have hne7 : p0 ≠ 7 := by omega
    have hne31 : p0 ≠ 31 := by omega
    have hne127 : p0 ≠ 127 := by omega
    let β : ℕ → ℚ := fun p =>
      if p = 3 then 56 / 41
      else if p = p0 then 1 + 1 / (p0 : ℚ)
      else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    refine graham_contra (z := 181) (zB := (1448 / 1446) * (2896 / 2894) * ((181 : ℚ) ^ 2 / ((181 : ℚ) ^ 2 - 3)))
      hP (by norm_num) hm he2 E β ?_ ?_ ?_ (fun L hLp hL181 hLβ => leaf181_bound hLp hL181 hLβ) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3 hp0
      · subst h3; norm_num
      · subst hp0; exact ⟨le_rfl, one_add_le_B hp0p.two_le⟩
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c _ hcd _ hne
      dsimp only [β] at hne
      split_ifs at hne with hc3 hcp0
      · subst hc3
        have hpeq : p = p0 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp p0 hp0P hcd (by omega)
        rw [hpeq]
        dsimp only [β]
        simp only [hne3, ↓reduceIte]
        have hp0q : (41 : ℚ) ≤ (p0 : ℚ) := by exact_mod_cast hp041
        have hdiv : (1 : ℚ) / (p0 : ℚ) ≤ 1 / 41 := one_div_le_one_div_of_le (by norm_num) hp0q
        linarith
      · rw [hcp0] at hcd
        exact absurd hcd (S4 p0 hp0p hp02 (hnz (by omega)) hp0d p hp)
      · exact absurd rfl hne
    · dsimp only [β]; norm_num [hne7.symm, hne31.symm, hne127.symm]
    · dsimp only [β]; norm_num [hne7.symm, hne31.symm, hne127.symm]
  · -- Subcase 181.c: m = 2 mod 4 -> 5 | 2^m + 1, so 5 in P, 3 in P, beta 5 = 6/5, beta 3 = 8/5.
    have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
    have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
    have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 5 h5P (by norm_num)
    by_cases h13P : 13 ∈ P
    · -- 13 in P -> 7 in P -> 31 not in P by weight_kill [3, 5, 7, 13, 31].
      have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 h13P (by norm_num)
      have h31P : 31 ∉ P := fun h31 =>
        weight_kill hP E (L := [3, 5, 7, 13, 31]) (by decide) (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
      by_cases h103P : 103 ∈ P
      · -- 13 in P, 103 in P -> 127 not in P by weight_kill [3, 5, 7, 13, 103, 127].
        have h127P : 127 ∉ P := fun h127 =>
          weight_kill hP E (L := [3, 5, 7, 13, 103, 127]) (by decide) (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
        let β : ℕ → ℚ := fun p =>
          if p = 3 then 8 / 5
          else if p = 5 then 6 / 5
          else if p = 31 then 1
          else if p = 127 then 1
          else if p = 103 then (104 / 103) * (824 / 822)
          else if p = 13 then (14 / 13) * ((104 / 103) * (824 / 822))
          else if p = 7 then (8 / 7) * ((14 / 13) * ((104 / 103) * (824 / 822)))
          else ((p : ℚ) + 1) / ((p : ℚ) - 1)
        refine graham_contra (z := 181)
          (zB := (1448 / 1446) * (2896 / 2894) * ((181 : ℚ) ^ 2 / ((181 : ℚ) ^ 2 - 3)))
          hP (by norm_num) hm he2 E β ?_ ?_ ?_ (fun L hLp hL181 hLβ => leaf181_bound hLp hL181 hLβ) ?_
        · intro p hp
          dsimp only [β]
          split_ifs with h3 h5 h31 h127 h103 h13 h7
          · subst h3; norm_num
          · subst h5; norm_num
          · exact absurd (h31 ▸ hp) h31P
          · exact absurd (h127 ▸ hp) h127P
          · subst h103; norm_num
          · subst h13; norm_num
          · subst h7; norm_num
          · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
        · intro p hp c hcP hcd hmin hne
          have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
            dsimp only [β]
            split_ifs with h3 h5 h31 h127 h103 h13 h7
            · subst h3; norm_num
            · subst h5; norm_num
            · exact absurd (h31 ▸ hp) h31P
            · exact absurd (h127 ▸ hp) h127P
            · subst h103; norm_num
            · subst h13; norm_num
            · subst h7; norm_num
            · exact le_rfl
          dsimp only [β] at hne
          split_ifs at hne with hc3 hc5 hc31 hc127 hc103 hc13 hc7
          · subst hc3
            have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
            rw [hpeq]; dsimp only [β]; norm_num
          · subst hc5
            exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
          · exact absurd (hc31 ▸ hcP) h31P
          · exact absurd (hc127 ▸ hcP) h127P
          · subst hc103
            have hp823 : 823 ≤ p := parent_ge_823_of_c103_z181 (hP p hp).1 (hP p hp).2 hcd hmin
            have hle : β p ≤ 824 / 822 := hBp.trans ((B_anti (by norm_num : 2 ≤ 823) hp823).trans (by norm_num))
            have hβc : β 103 = (104 / 103) * (824 / 822) := by dsimp only [β]; norm_num
            rw [hβc]
            have : (1 + 1 / (103 : ℚ)) * β p ≤ (1 + 1 / (103 : ℚ)) * (824 / 822) :=
              mul_le_mul_of_nonneg_left hle (by norm_num)
            linarith
          · subst hc13
            have hpeq : p = 103 := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 103 h103P hcd (by norm_num)
            rw [hpeq]; dsimp only [β]; norm_num
          · subst hc7
            have hpeq : p = 13 := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 13 h13P hcd (by norm_num)
            rw [hpeq]; dsimp only [β]; norm_num
          · exact absurd rfl hne
        · dsimp only [β]; norm_num
        · dsimp only [β]; norm_num
      · -- 13 in P, 103 not in P: 883 not in P (17 | 884 -> 9 | 18).
        have h883P : 883 ∉ P := fun h883 => by
          have h17P : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 883 h883 (by norm_num)
          exact S6 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 17 h17P (by norm_num)
        let β : ℕ → ℚ := fun p =>
          if p = 3 then 8 / 5
          else if p = 5 then 6 / 5
          else if p = 31 then 1
          else if p = 127 then (128 / 127) * (1001 / 999)
          else if p = 13 then (14 / 13) * (1001 / 999)
          else if p = 7 then (8 / 7) * ((14 / 13) * (1001 / 999))
          else ((p : ℚ) + 1) / ((p : ℚ) - 1)
        refine graham_contra (z := 181)
          (zB := (1448 / 1446) * (2896 / 2894) * ((181 : ℚ) ^ 2 / ((181 : ℚ) ^ 2 - 3)))
          hP (by norm_num) hm he2 E β ?_ ?_ ?_ (fun L hLp hL181 hLβ => leaf181_bound hLp hL181 hLβ) ?_
        · intro p hp
          dsimp only [β]
          split_ifs with h3 h5 h31 h127 h13 h7
          · subst h3; norm_num
          · subst h5; norm_num
          · exact absurd (h31 ▸ hp) h31P
          · subst h127; norm_num
          · subst h13; norm_num
          · subst h7; norm_num
          · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
        · intro p hp c hcP hcd hmin hne
          have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
            dsimp only [β]
            split_ifs with h3 h5 h31 h127 h13 h7
            · subst h3; norm_num
            · subst h5; norm_num
            · exact absurd (h31 ▸ hp) h31P
            · subst h127; norm_num
            · subst h13; norm_num
            · subst h7; norm_num
            · exact le_rfl
          dsimp only [β] at hne
          split_ifs at hne with hc3 hc5 hc31 hc127 hc13 hc7
          · subst hc3
            have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
            rw [hpeq]; dsimp only [β]; norm_num
          · subst hc5
            exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
          · exact absurd (hc31 ▸ hcP) h31P
          · subst hc127
            have hp1000 : 1000 ≤ p := parent_ge_1000_of_c127_z181 (hP p hp).1 (hP p hp).2 hcd hmin
            have hle : β p ≤ 1001 / 999 := hBp.trans ((B_anti (by norm_num : 2 ≤ 1000) hp1000).trans (by norm_num))
            have hβc : β 127 = (128 / 127) * (1001 / 999) := by dsimp only [β]; norm_num
            rw [hβc]
            have : (1 + 1 / (127 : ℚ)) * β p ≤ (1 + 1 / (127 : ℚ)) * (1001 / 999) :=
              mul_le_mul_of_nonneg_left hle (by norm_num)
            linarith
          · subst hc13
            have hp103 : p ≠ 103 := fun h => h103P (h ▸ hp)
            have hp883 : p ≠ 883 := fun h => h883P (h ▸ hp)
            have hp181 : p ≠ 181 := fun h => h181P (h ▸ hp)
            have hsq13 : ¬ 13 * 13 ∣ p + 1 := S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
            have hp1000 : 1000 ≤ p := parent_ge_1000_of_c13_z181 (hP p hp).1 (hP p hp).2
              hp103 hp883 hp181 hcd hmin hsq13
            have hle : β p ≤ 1001 / 999 := hBp.trans ((B_anti (by norm_num : 2 ≤ 1000) hp1000).trans (by norm_num))
            have hβc : β 13 = (14 / 13) * (1001 / 999) := by dsimp only [β]; norm_num
            rw [hβc]
            have : (1 + 1 / (13 : ℚ)) * β p ≤ (1 + 1 / (13 : ℚ)) * (1001 / 999) :=
              mul_le_mul_of_nonneg_left hle (by norm_num)
            linarith
          · subst hc7
            have hpeq : p = 13 := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 13 h13P hcd (by norm_num)
            rw [hpeq]; dsimp only [β]; norm_num
          · exact absurd rfl hne
        · dsimp only [β]; norm_num
        · dsimp only [β]; norm_num
    · -- 13 not in P: beta 7 = (8/7) * B(223), beta 61 = (62/61) * B(487), beta 31 = (32/31) * beta 61.
      let β : ℕ → ℚ := fun p =>
        if p = 3 then 8 / 5
        else if p = 5 then 6 / 5
        else if p = 7 then (8 / 7) * (224 / 222)
        else if p = 61 then (62 / 61) * (488 / 486)
        else if p = 31 then (32 / 31) * ((62 / 61) * (488 / 486))
        else ((p : ℚ) + 1) / ((p : ℚ) - 1)
      refine graham_contra (z := 181)
        (zB := (1448 / 1446) * (2896 / 2894) * ((181 : ℚ) ^ 2 / ((181 : ℚ) ^ 2 - 3)))
        hP (by norm_num) hm he2 E β ?_ ?_ ?_ (fun L hLp hL181 hLβ => leaf181_bound hLp hL181 hLβ) ?_
      · intro p hp
        dsimp only [β]
        split_ifs with h3 h5 h7 h61 h31
        · subst h3; norm_num
        · subst h5; norm_num
        · subst h7; norm_num
        · subst h61; norm_num
        · subst h31; norm_num
        · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
      · intro p hp c _ hcd hmin hne
        have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
          dsimp only [β]
          split_ifs with h3 h5 h7 h61 h31
          · subst h3; norm_num
          · subst h5; norm_num
          · subst h7; norm_num
          · subst h61; norm_num
          · subst h31; norm_num
          · exact le_rfl
        dsimp only [β] at hne
        split_ifs at hne with hc3 hc5 hc7 hc61 hc31
        · subst hc3
          have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
          rw [hpeq]; dsimp only [β]; norm_num
        · subst hc5
          exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
        · subst hc7
          have hp181 : p ≠ 181 := fun h => h181P (h ▸ hp)
          have hp13 : p ≠ 13 := fun h => h13P (h ▸ hp)
          have hsq7 : ¬ 7 * 7 ∣ p + 1 := S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
          have hp223 : 223 ≤ p := (parent_ge_of_c7 (hP p hp).1 (hP p hp).2 hp181 hp13
            (by norm_num) (by norm_num) (by norm_num) hcd hmin hsq7).1 rfl
          have hle : β p ≤ 224 / 222 := hBp.trans ((B_anti (by norm_num : 2 ≤ 223) hp223).trans (by norm_num))
          have hβc : β 7 = (8 / 7) * (224 / 222) := by dsimp only [β]; norm_num
          rw [hβc]
          have : (1 + 1 / (7 : ℚ)) * β p ≤ (1 + 1 / (7 : ℚ)) * (224 / 222) :=
            mul_le_mul_of_nonneg_left hle (by norm_num)
          linarith
        · subst hc61
          have hp487 : 487 ≤ p := parent_ge_487_of_c61_z181 (hP p hp).1 (hP p hp).2 hcd
          have hle : β p ≤ 488 / 486 := hBp.trans ((B_anti (by norm_num : 2 ≤ 487) hp487).trans (by norm_num))
          have hβc : β 61 = (62 / 61) * (488 / 486) := by dsimp only [β]; norm_num
          rw [hβc]
          have : (1 + 1 / (61 : ℚ)) * β p ≤ (1 + 1 / (61 : ℚ)) * (488 / 486) :=
            mul_le_mul_of_nonneg_left hle (by norm_num)
          linarith
        · subst hc31
          by_cases hp61 : p = 61
          · rw [hp61]; dsimp only [β]; norm_num
          · have hp487 : 487 ≤ p := parent_ge_487_of_c31_z181 (hP p hp).1 (hP p hp).2 hp61 hcd hmin
            have hle : β p ≤ 488 / 486 := hBp.trans ((B_anti (by norm_num : 2 ≤ 487) hp487).trans (by norm_num))
            have hβc : β 31 = (32 / 31) * ((62 / 61) * (488 / 486)) := by dsimp only [β]; norm_num
            rw [hβc]
            have : (1 + 1 / (31 : ℚ)) * β p ≤ (1 + 1 / (31 : ℚ)) * (488 / 486) :=
              mul_le_mul_of_nonneg_left hle (by norm_num)
            linarith
        · exact absurd rfl hne
      · dsimp only [β]; norm_num
      · dsimp only [β]; norm_num

-- Section 4. Elimination of z = 11 for m odd and 4 | m, and forcing 7 | n, ¬ 13 | n for m = 2 mod 4.

theorem z11_61_31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (he : e % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) :
    61 ∣ 1 + 11 ^ e ∧ 61 ∈ P ∧ 31 ∈ P := by
  have hK := prime_dvd_prime_pow (e := e) (z := 11) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 11 → c ∉ ({11} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, -, -, -, -, S7, -⟩ := facts hP hK E
  have hd : 1 + 11 ^ 2 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (z := 11) (e0 := 2) he
  have h61d : 61 ∣ 1 + 11 ^ e := Dvd.dvd.trans (by norm_num) hd
  have h61P : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) h61d
  have h31P : 31 ∈ P := S1 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 61 h61P (by norm_num)
  exact ⟨h61d, h61P, h31P⟩

theorem kill_z11_odd {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h11P : 11 ∉ P) (hm : 20 ≤ m) (he : e % 4 = 2) (hodd : m % 2 = 1)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) :
    False := by
  have he2 : 2 ≤ e := by omega
  have hK := prime_dvd_prime_pow (e := e) (z := 11) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 11 → c ∉ ({11} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, S3, S4, -, S6, -, S8⟩ := facts hP hK E
  obtain ⟨h61d, h61P, -⟩ := z11_61_31 hP he E
  have h3m : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one hodd
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 4 / 3
    else if p = 61 then 62 / 61
    else if p = 31 then 64 / 61
    else if p = 13 then (14 / 13) * (104 / 102)
    else if p = 7 then (8 / 7) * ((14 / 13) * (104 / 102))
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  refine graham_contra (z := 11)
    (zB := (44 / 42) * (704 / 702) * ((11 : ℚ) ^ 2 / ((11 : ℚ) ^ 2 - 3)))
    hP (by norm_num) hm he2 E β ?_ ?_ ?_ (fun L hLp hL11 hLβ => leaf11_bound hLp hL11 hLβ) ?_
  · intro p hp
    dsimp only [β]
    split_ifs with h3 h61 h31 h13 h7
    · subst h3; norm_num
    · subst h61; norm_num
    · subst h31; norm_num
    · subst h13; norm_num
    · subst h7; norm_num
    · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c _ hcd hmin hne
    have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
      dsimp only [β]
      split_ifs with h3 h61 h31 h13 h7
      · subst h3; norm_num
      · subst h61; norm_num
      · subst h31; norm_num
      · subst h13; norm_num
      · subst h7; norm_num
      · exact le_rfl
    dsimp only [β] at hne
    split_ifs at hne with hc3 hc61 hc31 hc13 hc7
    · subst hc3
      exact absurd hcd (S4 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) h3m p hp)
    · subst hc61
      exact absurd hcd (S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) h61d p hp)
    · subst hc31
      have hpeq : p = 61 := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 61 h61P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc13
      have hp103 : 103 ≤ p := parent_ge_103_of_c13_z11 (hP p hp).1 (hP p hp).2 hcd
      have hle : β p ≤ 104 / 102 := hBp.trans ((B_anti (by norm_num : 2 ≤ 103) hp103).trans (by norm_num))
      have hβc : β 13 = (14 / 13) * (104 / 102) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (13 : ℚ)) * β p ≤ (1 + 1 / (13 : ℚ)) * (104 / 102) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    · subst hc7
      by_cases hp13 : p = 13
      · rw [hp13]; dsimp only [β]; norm_num
      · have hp11 : p ≠ 11 := fun h => h11P (h ▸ hp)
        have hsq7 : ¬ 7 * 7 ∣ p + 1 := S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
        have hp181 : 181 ≤ p := (parent_ge_of_c7 (hP p hp).1 (hP p hp).2 hp11 hp13
          (by norm_num) (by norm_num) (by norm_num) hcd hmin hsq7).2 rfl
        have hle : β p ≤ 182 / 180 := hBp.trans ((B_anti (by norm_num : 2 ≤ 181) hp181).trans (by norm_num))
        have hβc : β 7 = (8 / 7) * ((14 / 13) * (104 / 102)) := by dsimp only [β]; norm_num
        rw [hβc]
        have : (1 + 1 / (7 : ℚ)) * β p ≤ (1 + 1 / (7 : ℚ)) * (182 / 180) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith
    · exact absurd rfl hne
  · dsimp only [β]; norm_num
  · dsimp only [β]; norm_num

theorem kill_z11_div4 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h11P : 11 ∉ P) (hm : 20 ≤ m) (he : e % 4 = 2) (hm4 : m % 4 = 0)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) :
    False := by
  have he2 : 2 ≤ e := by omega
  have hK := prime_dvd_prime_pow (e := e) (z := 11) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 11 → c ∉ ({11} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, S3, S4, -, S6, -, S8⟩ := facts hP hK E
  obtain ⟨h61d, h61P, -⟩ := z11_61_31 hP he E
  obtain ⟨k, hmk⟩ : ∃ k, m = 4 * k := ⟨m / 4, by omega⟩
  obtain ⟨p0, hp0P, hp0d, hp03, hp041⟩ := exists_p0_ge_41 hP (z := 11) (by norm_num) (by norm_num) (by omega)
    (fun p _ hd _ heq => not_dvd_two_pow_four_mul (k := k) (p := 11) (m := 5)
      (by norm_num) (by norm_num) ⟨2, by norm_num⟩ (by norm_num) (by rw [← hmk]; exact heq ▸ hd))
    E hm4
  have hp0p : p0.Prime := (hP p0 hp0P).1
  have hp02 : p0 ≠ 2 := (hP p0 hp0P).2
  have hne3 : p0 ≠ 3 := by omega
  have hne7 : p0 ≠ 7 := by omega
  have hne13 : p0 ≠ 13 := by omega
  have hne31 : p0 ≠ 31 := by omega
  have hne61 : p0 ≠ 61 := by omega
  have hne127 : p0 ≠ 127 := by omega
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 56 / 41
    else if p = 61 then 62 / 61
    else if p = 31 then 64 / 61
    else if p = 13 then (14 / 13) * (104 / 102)
    else if p = 7 then (8 / 7) * ((14 / 13) * (104 / 102))
    else if p = p0 then 1 + 1 / (p0 : ℚ)
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  refine graham_contra (z := 11)
    (zB := (44 / 42) * (704 / 702) * ((11 : ℚ) ^ 2 / ((11 : ℚ) ^ 2 - 3)))
    hP (by norm_num) hm he2 E β ?_ ?_ ?_ (fun L hLp hL11 hLβ => leaf11_bound hLp hL11 hLβ) ?_
  · intro p hp
    dsimp only [β]
    split_ifs with h3 h61 h31 h13 h7 hp0
    · subst h3; norm_num
    · subst h61; norm_num
    · subst h31; norm_num
    · subst h13; norm_num
    · subst h7; norm_num
    · subst hp0; exact ⟨le_rfl, one_add_le_B hp0p.two_le⟩
    · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c _ hcd hmin hne
    have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
      dsimp only [β]
      split_ifs with h3 h61 h31 h13 h7 hp0
      · subst h3; norm_num
      · subst h61; norm_num
      · subst h31; norm_num
      · subst h13; norm_num
      · subst h7; norm_num
      · subst hp0; exact one_add_le_B hp0p.two_le
      · exact le_rfl
    dsimp only [β] at hne
    split_ifs at hne with hc3 hc61 hc31 hc13 hc7 hcp0
    · subst hc3
      have hpeq : p = p0 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp p0 hp0P hcd (by omega)
      rw [hpeq]
      dsimp only [β]
      simp only [hne3, hne61, hne31, hne13, hne7, ↓reduceIte]
      have hp0q : (41 : ℚ) ≤ (p0 : ℚ) := by exact_mod_cast hp041
      have hdiv : (1 : ℚ) / (p0 : ℚ) ≤ 1 / 41 := one_div_le_one_div_of_le (by norm_num) hp0q
      linarith
    · subst hc61
      exact absurd hcd (S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) h61d p hp)
    · subst hc31
      have hpeq : p = 61 := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 61 h61P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc13
      have hp103 : 103 ≤ p := parent_ge_103_of_c13_z11 (hP p hp).1 (hP p hp).2 hcd
      have hle : β p ≤ 104 / 102 := hBp.trans ((B_anti (by norm_num : 2 ≤ 103) hp103).trans (by norm_num))
      have hβc : β 13 = (14 / 13) * (104 / 102) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (13 : ℚ)) * β p ≤ (1 + 1 / (13 : ℚ)) * (104 / 102) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    · subst hc7
      by_cases hp13 : p = 13
      · rw [hp13]; dsimp only [β]; norm_num
      · have hp11 : p ≠ 11 := fun h => h11P (h ▸ hp)
        have hsq7 : ¬ 7 * 7 ∣ p + 1 := S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
        have hp181 : 181 ≤ p := (parent_ge_of_c7 (hP p hp).1 (hP p hp).2 hp11 hp13
          (by norm_num) (by norm_num) (by norm_num) hcd hmin hsq7).2 rfl
        have hle : β p ≤ 182 / 180 := hBp.trans ((B_anti (by norm_num : 2 ≤ 181) hp181).trans (by norm_num))
        have hβc : β 7 = (8 / 7) * ((14 / 13) * (104 / 102)) := by dsimp only [β]; norm_num
        rw [hβc]
        have : (1 + 1 / (7 : ℚ)) * β p ≤ (1 + 1 / (7 : ℚ)) * (182 / 180) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith
    · rw [hcp0] at hcd
      exact absurd hcd (S4 p0 hp0p hp02 (hnz (by omega)) hp0d p hp)
    · exact absurd rfl hne
  · dsimp only [β]; norm_num [hne127.symm]
  · dsimp only [β]; norm_num [hne127.symm]

theorem z11_mod2_7_13 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hm : 20 ≤ m) (he : e % 4 = 2) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) :
    7 ∈ P ∧ 13 ∉ P := by
  have he2 : 2 ≤ e := by omega
  have hK := prime_dvd_prime_pow (e := e) (z := 11) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 11 → c ∉ ({11} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, -, -, S8⟩ := facts hP hK E
  obtain ⟨h61d, h61P, h31P⟩ := z11_61_31 hP he E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 5 h5P (by norm_num)
  have h13 : 13 ∉ P := fun h13P => by
    have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 h13P (by norm_num)
    exact weight_kill hP E (L := [3, 5, 7, 13, 31]) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
  have h7 : 7 ∈ P := by
    by_contra h7P
    let β : ℕ → ℚ := fun p =>
      if p = 3 then 8 / 5
      else if p = 5 then 6 / 5
      else if p = 61 then 62 / 61
      else if p = 31 then 64 / 61
      else if p = 7 then 1
      else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    refine graham_contra (z := 11)
      (zB := (44 / 42) * (704 / 702) * ((11 : ℚ) ^ 2 / ((11 : ℚ) ^ 2 - 3)))
      hP (by norm_num) hm he2 E β ?_ ?_ ?_ (fun L hLp hL11 hLβ => leaf11_bound hLp hL11 hLβ) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3 h5 h61 h31 h7'
      · subst h3; norm_num
      · subst h5; norm_num
      · subst h61; norm_num
      · subst h31; norm_num
      · exact absurd (h7' ▸ hp) h7P
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c hcP hcd _ hne
      dsimp only [β] at hne
      split_ifs at hne with hc3 hc5 hc61 hc31 hc7'
      · subst hc3
        have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
        rw [hpeq]; dsimp only [β]; norm_num
      · subst hc5
        exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
      · subst hc61
        exact absurd hcd (S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) h61d p hp)
      · subst hc31
        have hpeq : p = 61 := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 61 h61P hcd (by norm_num)
        rw [hpeq]; dsimp only [β]; norm_num
      · exact absurd (hc7' ▸ hcP) h7P
      · exact absurd rfl hne
    · dsimp only [β]; norm_num
    · dsimp only [β]; norm_num
  exact ⟨h7, h13⟩

-- Section 5. Main reduction theorem.

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1.H2 := by
  rintro ⟨A1, hA1⟩ ⟨A2, hA2⟩
  refine ⟨max 20 (max A1 A2), fun n hn z hz hS he hzmem _ _ _ h20 h28 _ _ _ _ _ => ?_⟩
  by_cases ha : padicValNat 2 n ≤ 20
  · omega
  have ha20 : 20 ≤ padicValNat 2 n := by omega
  have hn0 : n ≠ 0 := hn.2.ne'
  have h2_eq : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hz_dvd, hsimple⟩ := simple_of_unique_repeated hn0 hS
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hz_dvd, hn0⟩
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  obtain ⟨hP, E⟩ := kernel_balance_one hn hzpf hz2 hsimple
  set P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ))
  have hzP : z ∉ P := fun h => (Finset.mem_filter.mp h).2 (Finset.mem_singleton_self z)
  have hm20 : 20 ≤ n.factorization 2 := h2_eq ▸ ha20
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
  rcases hzmem with rfl | rfl | rfl | rfl | rfl
  · -- z = 11
    have hmod4 : n.factorization 2 % 2 = 1 ∨ n.factorization 2 % 4 = 0 ∨ n.factorization 2 % 4 = 2 := by omega
    rcases hmod4 with hodd | hm4 | hm2
    · exact False.elim (kill_z11_odd hP hzP hm20 he hodd E)
    · exact False.elim (kill_z11_div4 hP hzP hm20 he hm4 E)
    · obtain ⟨h7P, h13P⟩ := z11_mod2_7_13 hP hm20 he hm2 E
      have h7d : 7 ∣ n := Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp h7P).1)
      have h13d : ¬ 13 ∣ n := fun hd => h13P (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨by norm_num, Nat.mem_primeFactors.mpr ⟨by norm_num, hd, hn0⟩⟩, by decide⟩)
      have ha4 : padicValNat 2 n % 4 = 2 := h2_eq ▸ hm2
      have ha28 : padicValNat 2 n % 28 ≠ 14 := h28 (by norm_num)
      by_cases he2 : n.factorization 11 = 2
      · have hle := hA1 n hn hS he2 ha4 h20 ha28 h7d h13d
        omega
      · have he6 : 6 ≤ n.factorization 11 := by omega
        have hle := hA2 n hn hS he6 he ha4 h20 ha28 h7d h13d
        omega
  · exact False.elim (kill_z139 hP (by omega) E he)
  · exact False.elim (kill_z181 hP hzP hm20 he E)
  · exact False.elim (kill_z199 hP (by omega) E he)
  · exact False.elim (kill_z271 hP (by omega) E he)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1
