import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1

/-!
# Proof of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H1

Credit: @sanchan (also acknowledging @aroth01's desk notes on this step).

Proves `H1` of `Erdos1052...H4.R1` directly with `A = 20` across all 69 primes `z` and odd `e`:
1. All 15 primes with `z ≡ 2 (mod 3)` fail unconditionally: `3 ∣ z + 1 ∣ 1 + z^e` and `a` is even;
   if `a ≡ 2 (mod 4)` then `5 ∣ 2^a + 1` forces `5 ∈ P` and `3 ∣ 5 + 1`, contradicting `S8`;
   if `4 ∣ a` then `2^a + 1 ≡ 2 (mod 3)` has a prime factor `c ≡ 2 (mod 3)`, which cannot equal `z`
   because `16` has odd multiplicative order modulo every one of these 15 primes.
2. 38 primes with `z ≡ 1 (mod 3)` fail unconditionally via a short forced chain from `z + 1` to
   a prime `q ≡ 2 (mod 3)`, contradicting `3 ∣ 2^a + 1` (for `a` odd) or unique source of `3`
   (for `a` even).
3. All 16 remaining primes (`7, 13, 31, 61, 103, 127, 223, 433, 487, 823, 853, 991, 1663, 1777,
   1783, 1951`) fail for all `a ≥ 20` via Graham weights (`master_gen`, `mersenne_bound`,
   `fiber_bound`, `zleaf_bound`) and `weight_kill`.
-/

namespace OMA.P_Erdos1052_H4_R1_H1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1 hiding H1 H2 H3 H4 main

-- Section 1. Mod-3, Fermat/order-of-16, and forced-chain kills (53 of 69 primes).

private theorem two_pow_mod_three_even {m : ℕ} (hm : m % 2 = 0) : (2 ^ m + 1) % 3 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  rw [pow_mul]
  have h4 : ∀ t : ℕ, (2 ^ 2) ^ t % 3 = 1 := fun t => by
    induction t with
    | zero => norm_num
    | succ t ih => rw [pow_succ, Nat.mul_mod, ih]; norm_num
  have := h4 k
  omega

private theorem not_dvd_two_pow_four_mul {p t k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : Odd t) (h16 : (16 : ZMod p) ^ t = 1) : ¬ p ∣ 2 ^ (4 * k) + 1 := by
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
  have hneg : (-1 : ZMod p) ^ t = 1 := by
    rw [← h16k, ← pow_mul, mul_comm, pow_mul, h16, one_pow]
  rw [ht.neg_one_pow] at hneg
  have h2z : (2 : ZMod p) = 0 := by linear_combination -hneg
  have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2z)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2d)

private theorem pow16_odd_of_mod4_eq3 {z : ℕ} (hz : z.Prime) (hz4 : z % 4 = 3) :
    ∃ t : ℕ, Odd t ∧ (16 : ZMod z) ^ t = 1 := by
  have : Fact z.Prime := ⟨hz⟩
  have hz2 : z ≠ 2 := by omega
  have h2ne : (2 : ZMod z) ≠ 0 := by
    intro h0
    have h2d : z ∣ 2 := (ZMod.natCast_eq_zero_iff 2 z).mp (by simpa using h0)
    exact hz2 ((Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp h2d)
  have hflt : (2 : ZMod z) ^ (z - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  refine ⟨(z - 1) / 2, ⟨(z - 3) / 4, by omega⟩, ?_⟩
  have h16 : (16 : ZMod z) = (2 : ZMod z) ^ 4 := by norm_num
  have hexp : 4 * ((z - 1) / 2) = (z - 1) * 2 := by omega
  rw [h16, ← pow_mul, hexp, pow_mul, hflt, one_pow]

private theorem dvd_one_add_pow_of_odd {z e : ℕ} (he : Odd e) : z + 1 ∣ 1 + z ^ e := by
  obtain ⟨Q, hQ, -⟩ := exists_quot_mod (z := z) he
  exact ⟨Q, hQ⟩

private theorem kill_z_mod3_2 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime) (hz7 : 7 ≤ z) (hz3 : z % 3 = 2) (hm0 : m ≠ 0) (hm_even : Even m) (he : Odd e)
    (h16 : ∃ t : ℕ, Odd t ∧ (16 : ZMod z) ^ t = 1)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP hK E
  have h3z : 3 ∣ 1 + z ^ e := Dvd.dvd.trans (by omega : 3 ∣ z + 1) (dvd_one_add_pow_of_odd he)
  have hm2 : m % 2 = 0 := Nat.even_iff.mp hm_even
  have hcases : m % 4 = 2 ∨ m % 4 = 0 := by omega
  rcases hcases with hm24 | hm04
  · have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by omega)) (five_dvd_two_pow_add_one hm24)
    exact S8 3 Nat.prime_three (by norm_num) (hnz (by omega)) h3z 5 h5P (by norm_num)
  · obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k := ⟨m / 4, by omega⟩
    obtain ⟨c, hcp, hcd, hc3⟩ := exists_prime_mod3 (2 ^ (4 * k) + 1) (two_pow_mod_three_even hm2)
    have hc2 : c ≠ 2 := by
      rintro rfl
      have h2m : 2 ∣ 2 ^ (4 * k) := dvd_pow_self 2 hm0
      have : 2 ∣ 1 := (Nat.dvd_add_right h2m).mp hcd
      omega
    obtain ⟨t, ht, h16t⟩ := h16
    have hcz : c ≠ z := fun heq => not_dvd_two_pow_four_mul hz (by omega) ht h16t (heq ▸ hcd)
    have hcP : c ∈ P := S2 c hcp hc2 (hnz hcz) hcd
    exact S8 3 Nat.prime_three (by norm_num) (hnz (by omega)) h3z c hcP (by omega)

private theorem kill_consumed_mod3_any {m e z q : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, x.Prime ∧ x ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 1) (hm0 : m ≠ 0)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ x ∈ P, (x + 1) = 2 ^ (m + 1) * z ^ e * ∏ x ∈ P, x)
    (hqP : q ∈ P) (hq3 : 3 ∣ q + 1)
    (hsrc : q ∣ 1 + z ^ e ∨ ∃ p ∈ P, q ∣ p + 1) : False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, S4, -, -, -, -⟩ := facts hP hK E
  rcases Nat.even_or_odd m with hm | hm
  · have hm2 : m % 2 = 0 := Nat.even_iff.mp hm
    obtain ⟨c, hcp, hcd, hc3⟩ := exists_prime_mod3 (2 ^ m + 1) (two_pow_mod_three_even hm2)
    have hc2 : c ≠ 2 := by
      rintro rfl
      have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 hm0
      have : 2 ∣ 1 := (Nat.dvd_add_right h2m).mp hcd
      omega
    have hcz : c ≠ z := by omega
    have hcP : c ∈ P := S2 c hcp hc2 (hnz hcz) hcd
    have hcq : c = q := S3 3 Nat.prime_three (by norm_num) (hnz (by omega)) c hcP q hqP (by omega) hq3
    rw [hcq] at hcd hcp hc2 hcz
    rcases hsrc with hqK | ⟨p, hpP, hqp⟩
    · exact S_sq hP hK E hcp hc2 (hnz hcz) ((mul_dvd_mul hcd hqK).mul_right _)
    · exact S4 q hcp hc2 (hnz hcz) hcd p hpP hqp
  · have h3m : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one (Nat.odd_iff.mp hm)
    exact S4 3 Nat.prime_three (by norm_num) (hnz (by omega)) h3m q hqP hq3

private theorem kill_c1 {m e z q : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, x.Prime ∧ x ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 1) (hm0 : m ≠ 0) (he : Odd e)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ x ∈ P, (x + 1) = 2 ^ (m + 1) * z ^ e * ∏ x ∈ P, x)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqz : q ≠ z) (hq3 : 3 ∣ q + 1) (hd : q ∣ z + 1) : False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, -, -, -, -, S7, -⟩ := facts hP hK E
  have hqK : q ∣ 1 + z ^ e := hd.trans (dvd_one_add_pow_of_odd he)
  exact kill_consumed_mod3_any hP hz hz3 hm0 E (S7 q hq hq2 (hnz hqz) hqK) hq3 (Or.inl hqK)

private theorem kill_c2 {m e z p1 q : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, x.Prime ∧ x ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 1) (hm0 : m ≠ 0) (he : Odd e)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ x ∈ P, (x + 1) = 2 ^ (m + 1) * z ^ e * ∏ x ∈ P, x)
    (hp1 : p1.Prime) (hp12 : p1 ≠ 2) (hp1z : p1 ≠ z) (hd1 : p1 ∣ z + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqz : q ≠ z) (hq3 : 3 ∣ q + 1) (hd2 : q ∣ p1 + 1) : False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, -, -, -, -, S7, -⟩ := facts hP hK E
  have hp1P : p1 ∈ P := S7 p1 hp1 hp12 (hnz hp1z) (hd1.trans (dvd_one_add_pow_of_odd he))
  have hqP : q ∈ P := S1 q hq hq2 (hnz hqz) p1 hp1P hd2
  exact kill_consumed_mod3_any hP hz hz3 hm0 E hqP hq3 (Or.inr ⟨p1, hp1P, hd2⟩)

private theorem kill_c3 {m e z p1 p2 q : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, x.Prime ∧ x ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 1) (hm0 : m ≠ 0) (he : Odd e)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ x ∈ P, (x + 1) = 2 ^ (m + 1) * z ^ e * ∏ x ∈ P, x)
    (hp1 : p1.Prime) (hp12 : p1 ≠ 2) (hp1z : p1 ≠ z) (hd1 : p1 ∣ z + 1)
    (hp2 : p2.Prime) (hp22 : p2 ≠ 2) (hp2z : p2 ≠ z) (hd2 : p2 ∣ p1 + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqz : q ≠ z) (hq3 : 3 ∣ q + 1) (hd3 : q ∣ p2 + 1) : False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, -, -, -, -, S7, -⟩ := facts hP hK E
  have hp1P : p1 ∈ P := S7 p1 hp1 hp12 (hnz hp1z) (hd1.trans (dvd_one_add_pow_of_odd he))
  have hp2P : p2 ∈ P := S1 p2 hp2 hp22 (hnz hp2z) p1 hp1P hd2
  have hqP : q ∈ P := S1 q hq hq2 (hnz hqz) p2 hp2P hd3
  exact kill_consumed_mod3_any hP hz hz3 hm0 E hqP hq3 (Or.inr ⟨p2, hp2P, hd3⟩)

-- Section 2. Generic z-leaf bounds, Graham wrapper, and 4 | m / odd m prime lower bound.

private theorem exists_p0_ge_41 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 1) (hm0 : m ≠ 0)
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
  have hp0z : p0 ≠ z := by omega
  have hp0P : p0 ∈ P := S2 p0 hp0p hp02 (hnz hp0z) hp0d
  refine ⟨p0, hp0P, hp0d, hp03, ?_⟩
  by_contra hlt
  push Not at hlt
  have h5 : p0 ≠ 5 := fun h => not_dvd_two_pow_four_mul (k := k) (p := 5) (t := 1)
    (by norm_num) (by norm_num) ⟨0, by norm_num⟩ (by decide) (h ▸ hp0d)
  have h11 : p0 ≠ 11 := fun h => not_dvd_two_pow_four_mul (k := k) (p := 11) (t := 5)
    (by norm_num) (by norm_num) ⟨2, by norm_num⟩ (by decide) (h ▸ hp0d)
  have h17 : p0 ≠ 17 := by
    rintro rfl
    exact S6 3 Nat.prime_three (by norm_num) (hnz (by omega)) 17 hp0P (by norm_num)
  have h23 : p0 ≠ 23 := fun h => not_dvd_two_pow_four_mul (k := k) (p := 23) (t := 11)
    (by norm_num) (by norm_num) ⟨5, by norm_num⟩ (by decide) (h ▸ hp0d)
  have h29 : p0 ≠ 29 := fun h => not_dvd_two_pow_four_mul (k := k) (p := 29) (t := 7)
    (by norm_num) (by norm_num) ⟨3, by norm_num⟩ (by decide) (h ▸ hp0d)
  interval_cases p0 <;>
    first | exact h5 rfl | exact h11 rfl | exact h17 rfl | exact h23 rfl | exact h29 rfl
          | omega | norm_num at hp0p

private theorem odd_pow_mod2 {z : ℕ} (hz : z % 2 = 1) : ∀ t : ℕ, (z ^ t) % 2 = 1 := fun t => by
  induction t with
  | zero => norm_num
  | succ t ih => rw [pow_succ, Nat.mul_mod, ih, hz]

private theorem leaf_decomp {z q : ℕ} (hz : z.Prime) (hz2 : z ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hzd : z ∣ q + 1) (huniq : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = z) :
    ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j := by
  obtain ⟨k, j, heq⟩ := two_pow_mul_pow_of_odd_primes_eq (by omega) huniq
  have hodd := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hzodd := Nat.odd_iff.mp (hz.odd_of_ne_two hz2)
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at heq
    have := odd_pow_mod2 hzodd j
    omega
  have hj1 : 1 ≤ j := by
    by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0, pow_zero, mul_one] at heq
    have hzd2 : z ∣ 2 ^ k := heq ▸ hzd
    exact hz2 ((Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow hzd2))
  exact ⟨k, j, hk1, hj1, heq⟩

private theorem zleaf_k6_bound {z : ℕ} (hz : z.Prime) (hz7 : 7 ≤ z) (S : Finset ℕ)
    (hS : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 ∈ S)
    {L : Finset ℕ} {β : ℕ → ℚ}
    (hLp : ∀ q ∈ L, q.Prime ∧ q ≠ 2)
    (hLz : ∀ q ∈ L, z ∣ q + 1 ∧ ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = z)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (hS1 : ∀ q ∈ S, 1 ≤ β q) :
    ∏ q ∈ L, β q ≤ (∏ q ∈ S, β q) * (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) *
      ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)) := by
  have hz2 : z ≠ 2 := by omega
  have hkj : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j :=
    fun q hq => leaf_decomp hz hz2 (hLp q hq).1 (hLp q hq).2 (hLz q hq).1 (hLz q hq).2
  rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => ¬ z ^ 2 ∣ q + 1)]
  have hpart2 : ∏ q ∈ L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1), β q ≤
      (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) := by
    have hB : ∏ q ∈ L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1), β q ≤
        ∏ q ∈ L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod (fun q hq => (hLβ q (Finset.mem_filter.mp hq).1).1.le)
        (fun q hq => (hLβ q (Finset.mem_filter.mp hq).1).2)
    refine hB.trans (zleaf_bound (z := z) (by omega) 2 (by norm_num) _ (fun q hq => ?_))
    obtain ⟨hqL, hdiv⟩ := Finset.mem_filter.mp hq
    push Not at hdiv
    obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
    refine ⟨k, j, hk1, ?_, heq⟩
    by_contra hjlt
    have hj : j = 1 := by omega
    rw [heq, hj, pow_one] at hdiv
    have hz2k : z ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_right hz.pos (by simpa [sq] using hdiv)
    exact hz2 ((Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow hz2k))
  have hpart1 : ∏ q ∈ L.filter (fun q => ¬ z ^ 2 ∣ q + 1), β q ≤
      (∏ q ∈ S, β q) * (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not _ (fun q => q ∈ S)]
    have hsmall : ∏ q ∈ (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => q ∈ S), β q ≤
        ∏ q ∈ S, β q := by
      have hsub : (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => q ∈ S) ⊆ S :=
        fun q hq => (Finset.mem_filter.mp hq).2
      exact Finset.prod_le_prod_of_subset_of_one_le hsub
        (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.le)
        (fun q hq _ => hS1 q hq)
    have hgt : ∏ q ∈ (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ q ∈ S), β q ≤
        ((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2) := by
      have hB : ∏ q ∈ (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ q ∈ S), β q ≤
          ∏ q ∈ (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ q ∈ S),
            (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
        Finset.prod_le_prod
          (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.le)
          (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2)
      refine hB.trans (fiber_bound (u := 64 * z) (by omega) _ (fun q hq => ?_))
      obtain ⟨hq1, hnotS⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, hndiv⟩ := Finset.mem_filter.mp hq1
      obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
      have hj : j = 1 := by
        by_contra hne1
        apply hndiv
        rw [heq]
        exact dvd_mul_of_dvd_right (pow_dvd_pow z (by omega : 2 ≤ j)) _
      rw [hj, pow_one] at heq
      have hk7 : 7 ≤ k := by
        by_contra hklt
        have hqeq : q = 2 ^ k * z - 1 := by omega
        have hmem := hS k (Finset.mem_Icc.mpr ⟨hk1, by omega⟩) (hqeq ▸ (hLp q hqL).1)
        exact hnotS (hqeq.symm ▸ hmem)
      refine ⟨k - 6, by omega, ?_⟩
      have hk_eq : (k - 6) + 6 = k := by omega
      have heq' : q + 1 = 2 ^ ((k - 6) + 6) * z := by rwa [hk_eq]
      rw [heq', pow_add]
      ring
    exact mul_le_mul hsmall hgt
      (Finset.prod_nonneg fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.le)
      (Finset.prod_nonneg fun q hq => le_trans zero_le_one (hS1 q hq))
  have hSpos : (0 : ℚ) ≤ ∏ q ∈ S, β q := Finset.prod_nonneg fun q hq => le_trans zero_le_one (hS1 q hq)
  have h64pos : (0 : ℚ) ≤ ((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2) := by
    have : (7 : ℚ) ≤ z := by exact_mod_cast hz7
    push_cast; exact div_nonneg (by nlinarith) (by nlinarith)
  exact mul_le_mul hpart1 hpart2
    (Finset.prod_nonneg fun q hq => (hLβ q (Finset.mem_filter.mp hq).1).1.le)
    (mul_nonneg hSpos h64pos)

private theorem zleaf_k6_j2_bound {z : ℕ} (hz : z.Prime) (hz7 : 7 ≤ z) (S1 S2 : Finset ℕ)
    (hS1 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 ∈ S1)
    (hS2 : ∀ k ∈ Finset.Icc 1 4, (2 ^ k * z ^ 2 - 1).Prime → 2 ^ k * z ^ 2 - 1 ∈ S2)
    {L : Finset ℕ} {β : ℕ → ℚ}
    (hLp : ∀ q ∈ L, q.Prime ∧ q ≠ 2)
    (hLz : ∀ q ∈ L, z ∣ q + 1 ∧ ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = z)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (hS1_1 : ∀ q ∈ S1, 1 ≤ β q) (hS2_1 : ∀ q ∈ S2, 1 ≤ β q) :
    ∏ q ∈ L, β q ≤ ((∏ q ∈ S1, β q) * (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2))) *
      (((∏ q ∈ S2, β q) * (((16 * z ^ 2 : ℕ) : ℚ) / ((16 * z ^ 2 : ℕ) - 2))) *
        ((z : ℚ) ^ 3 / ((z : ℚ) ^ 3 - 3))) := by
  have hz2 : z ≠ 2 := by omega
  have hkj : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j :=
    fun q hq => leaf_decomp hz hz2 (hLp q hq).1 (hLp q hq).2 (hLz q hq).1 (hLz q hq).2
  rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => ¬ z ^ 2 ∣ q + 1)]
  have hpart1 : ∏ q ∈ L.filter (fun q => ¬ z ^ 2 ∣ q + 1), β q ≤
      (∏ q ∈ S1, β q) * (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not _ (fun q => q ∈ S1)]
    have hsmall : ∏ q ∈ (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => q ∈ S1), β q ≤
        ∏ q ∈ S1, β q :=
      Finset.prod_le_prod_of_subset_of_one_le (fun q hq => (Finset.mem_filter.mp hq).2)
        (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.le)
        (fun q hq _ => hS1_1 q hq)
    have hgt : ∏ q ∈ (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ q ∈ S1), β q ≤
        ((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2) := by
      have hB : ∏ q ∈ (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ q ∈ S1), β q ≤
          ∏ q ∈ (L.filter (fun q => ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ q ∈ S1),
            (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
        Finset.prod_le_prod
          (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.le)
          (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2)
      refine hB.trans (fiber_bound (u := 64 * z) (by omega) _ (fun q hq => ?_))
      obtain ⟨hq1, hnotS⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, hndiv⟩ := Finset.mem_filter.mp hq1
      obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
      have hj : j = 1 := by
        by_contra hne1
        apply hndiv
        rw [heq]
        exact dvd_mul_of_dvd_right (pow_dvd_pow z (by omega : 2 ≤ j)) _
      rw [hj, pow_one] at heq
      have hk7 : 7 ≤ k := by
        by_contra hklt
        have hqeq : q = 2 ^ k * z - 1 := by omega
        have hmem := hS1 k (Finset.mem_Icc.mpr ⟨hk1, by omega⟩) (hqeq ▸ (hLp q hqL).1)
        exact hnotS (hqeq.symm ▸ hmem)
      refine ⟨k - 6, by omega, ?_⟩
      have hk_eq : (k - 6) + 6 = k := by omega
      have heq' : q + 1 = 2 ^ ((k - 6) + 6) * z := by rwa [hk_eq]
      rw [heq', pow_add]
      ring
    exact mul_le_mul hsmall hgt
      (Finset.prod_nonneg fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.le)
      (Finset.prod_nonneg fun q hq => le_trans zero_le_one (hS1_1 q hq))
  have hpart23 : ∏ q ∈ L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1), β q ≤
      ((∏ q ∈ S2, β q) * (((16 * z ^ 2 : ℕ) : ℚ) / ((16 * z ^ 2 : ℕ) - 2))) *
        ((z : ℚ) ^ 3 / ((z : ℚ) ^ 3 - 3)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not _ (fun q => ¬ z ^ 3 ∣ q + 1)]
    have hpart3 : ∏ q ∈ (L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ ¬ z ^ 3 ∣ q + 1), β q ≤
        (z : ℚ) ^ 3 / ((z : ℚ) ^ 3 - 3) := by
      have hB : ∏ q ∈ (L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ ¬ z ^ 3 ∣ q + 1), β q ≤
          ∏ q ∈ (L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ ¬ z ^ 3 ∣ q + 1),
            (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
        Finset.prod_le_prod
          (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.le)
          (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2)
      refine hB.trans (zleaf_bound (z := z) (by omega) 3 (by norm_num) _ (fun q hq => ?_))
      obtain ⟨hq1, hdiv3⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, -⟩ := Finset.mem_filter.mp hq1
      push Not at hdiv3
      obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
      refine ⟨k, j, hk1, ?_, heq⟩
      by_contra hjlt
      have hj2 : j ≤ 2 := by omega
      have hpow : z ^ j ∣ z ^ 2 := pow_dvd_pow z hj2
      have h32 : z * z ^ 2 ∣ 2 ^ k * z ^ 2 := by
        have h1 : z ^ 3 ∣ 2 ^ k * z ^ j := heq ▸ hdiv3
        have h2 : z ^ 3 ∣ 2 ^ k * z ^ 2 := h1.trans (Nat.mul_dvd_mul_left _ hpow)
        simpa [pow_succ'] using h2
      have hz2k : z ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_right (pow_pos hz.pos 2) h32
      exact hz2 ((Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow hz2k))
    have hpart2 : ∏ q ∈ (L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ z ^ 3 ∣ q + 1), β q ≤
        (∏ q ∈ S2, β q) * (((16 * z ^ 2 : ℕ) : ℚ) / ((16 * z ^ 2 : ℕ) - 2)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not _ (fun q => q ∈ S2)]
      have hsmall : ∏ q ∈ ((L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ z ^ 3 ∣ q + 1)).filter (fun q => q ∈ S2), β q ≤
          ∏ q ∈ S2, β q :=
        Finset.prod_le_prod_of_subset_of_one_le (fun q hq => (Finset.mem_filter.mp hq).2)
          (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1).1.le)
          (fun q hq _ => hS2_1 q hq)
      have hgt : ∏ q ∈ ((L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ z ^ 3 ∣ q + 1)).filter (fun q => ¬ q ∈ S2), β q ≤
          ((16 * z ^ 2 : ℕ) : ℚ) / ((16 * z ^ 2 : ℕ) - 2) := by
        have hB : ∏ q ∈ ((L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ z ^ 3 ∣ q + 1)).filter (fun q => ¬ q ∈ S2), β q ≤
            ∏ q ∈ ((L.filter (fun q => ¬ ¬ z ^ 2 ∣ q + 1)).filter (fun q => ¬ z ^ 3 ∣ q + 1)).filter (fun q => ¬ q ∈ S2),
              (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
          Finset.prod_le_prod
            (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1).1.le)
            (fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1).2)
        refine hB.trans (fiber_bound (u := 16 * z ^ 2) (by nlinarith) _ (fun q hq => ?_))
        obtain ⟨hq2, hnotS2⟩ := Finset.mem_filter.mp hq
        obtain ⟨hq1, hndiv3⟩ := Finset.mem_filter.mp hq2
        obtain ⟨hqL, hdiv2⟩ := Finset.mem_filter.mp hq1
        push Not at hdiv2
        obtain ⟨k, j, hk1, hj1, heq⟩ := hkj q hqL
        have hjge2 : 2 ≤ j := by
          by_contra hjlt
          have hj1' : j = 1 := by omega
          rw [heq, hj1', pow_one] at hdiv2
          have hz2k : z ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_right hz.pos (by simpa [sq] using hdiv2)
          exact hz2 ((Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp (hz.dvd_of_dvd_pow hz2k))
        have hj : j = 2 := by
          by_contra hne2
          apply hndiv3
          rw [heq]
          exact dvd_mul_of_dvd_right (pow_dvd_pow z (by omega : 3 ≤ j)) _
        rw [hj] at heq
        have hk5 : 5 ≤ k := by
          by_contra hklt
          have hqeq : q = 2 ^ k * z ^ 2 - 1 := by omega
          have hmem := hS2 k (Finset.mem_Icc.mpr ⟨hk1, by omega⟩) (hqeq ▸ (hLp q hqL).1)
          exact hnotS2 (hqeq.symm ▸ hmem)
        refine ⟨k - 4, by omega, ?_⟩
        have hk_eq : (k - 4) + 4 = k := by omega
        have heq' : q + 1 = 2 ^ ((k - 4) + 4) * z ^ 2 := by rwa [hk_eq]
        rw [heq', pow_add]
        ring
      exact mul_le_mul hsmall hgt
        (Finset.prod_nonneg fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1).1.le)
        (Finset.prod_nonneg fun q hq => le_trans zero_le_one (hS2_1 q hq))
    have hS2pos : (0 : ℚ) ≤ ∏ q ∈ S2, β q := Finset.prod_nonneg fun q hq => le_trans zero_le_one (hS2_1 q hq)
    have h16pos : (0 : ℚ) ≤ ((16 * z ^ 2 : ℕ) : ℚ) / ((16 * z ^ 2 : ℕ) - 2) := by
      have : (7 : ℚ) ≤ z := by exact_mod_cast hz7
      push_cast; exact div_nonneg (by nlinarith) (by nlinarith)
    exact mul_le_mul hpart2 hpart3
      (Finset.prod_nonneg fun q hq => (hLβ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1.le)
      (mul_nonneg hS2pos h16pos)
  have hS1pos : (0 : ℚ) ≤ ∏ q ∈ S1, β q := Finset.prod_nonneg fun q hq => le_trans zero_le_one (hS1_1 q hq)
  have h64pos : (0 : ℚ) ≤ ((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2) := by
    have : (7 : ℚ) ≤ z := by exact_mod_cast hz7
    push_cast; exact div_nonneg (by nlinarith) (by nlinarith)
  exact mul_le_mul hpart1 hpart23
    (Finset.prod_nonneg fun q hq => (hLβ q (Finset.mem_filter.mp hq).1).1.le)
    (mul_nonneg hS1pos h64pos)

private theorem graham_contra {m e z e0 : ℕ} {P : Finset ℕ} {zB : ℚ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hm : 20 ≤ m) (he : e0 ≤ e)
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
    (hnum : (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ e0) *
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
  have hze : ((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ) ≤ 1 + 1 / (z : ℚ) ^ e0 := by
    have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hz.one_le
    have hpow : (z : ℚ) ^ e0 ≤ (z : ℚ) ^ e := pow_le_pow_right₀ hz1 he
    have hpos : (0 : ℚ) < (z : ℚ) ^ e0 := by positivity
    have hpos2 : (0 : ℚ) < (z : ℚ) ^ e := by positivity
    have hdiv := one_div_le_one_div_of_le hpos hpow
    push_cast
    rw [add_div, div_self hpos2.ne']
    linarith
  have hfac : (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) ≤
      (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ e0) :=
    mul_le_mul h2m hze (by positivity) (by positivity)
  have htot := mul_le_mul hfac hprod
    (mul_nonneg (Finset.prod_nonneg fun q hq => (hLpos q (Finset.mem_filter.mp hq).1).1.le)
      (Finset.prod_nonneg fun q hq => (hLpos q (Finset.mem_filter.mp hq).1).1.le))
    (by positivity)
  linarith

-- Section 3. Uniform kill for ALL 16 surviving primes when m odd or 4 | m (m >= 20).

private theorem kill_not_mod2_generic {m e z e0 : ℕ} {P : Finset ℕ} (S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hz7 : 7 ≤ z) (hz3 : z % 3 = 1) (hzP : z ∉ P)
    (hm : 20 ≤ m) (he : e0 ≤ e) (hnm2 : m % 4 ≠ 2)
    (hS : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 ∈ S)
    (hS_ne3 : 3 ∉ S) (hS_nez : z ∉ S) (hS_ne7 : 7 ∉ S) (hS_mod3 : ∀ q ∈ S, q % 3 ≠ 2)
    (hS_gt1 : ∀ q ∈ S, 2 ≤ q)
    (h7kill : z = 13 → 7 ∣ 1 + z ^ e)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hnum : (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ e0) *
      (((56 / 41 : ℚ) * (if z = 7 then 1 else if z = 13 then 8 / 7 else 8 / 6) *
        (if z = 31 then 1 else 32 / 30) * (if z = 127 then 1 else 128 / 126)) *
        (2048 / 2047) *
        ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) *
          ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)))) < 2) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, S3, S4, -, -, -, S8⟩ := facts hP hK E
  have hcases : m % 2 = 1 ∨ m % 4 = 0 := by omega
  rcases hcases with hodd | hm4
  · have h3m : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one hodd
    let β : ℕ → ℚ := fun p =>
      if p = 3 then 4 / 3
      else if p = z then 1
      else if z = 13 ∧ p = 7 then 8 / 7
      else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    have hSβ : ∀ q ∈ S, β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
      dsimp only [β]
      have hq3 : q ≠ 3 := fun h => hS_ne3 (h ▸ hq)
      have hqz : q ≠ z := fun h => hS_nez (h ▸ hq)
      have hq7 : q ≠ 7 := fun h => hS_ne7 (h ▸ hq)
      simp only [hq3, hqz, hq7, and_false, ↓reduceIte]
    refine graham_contra (e0 := e0) hP hz hm he E β ?_ ?_ ?_
      (fun L hLp hLz hLβ => by
        have h := zleaf_k6_bound hz hz7 S hS hLp hLz hLβ (fun q hq => by
          rw [hSβ q hq]
          have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hS_gt1 q hq
          rw [le_div_iff₀ (by linarith)]; linarith)
        simpa only [Finset.prod_congr rfl hSβ] using h) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3 hpz h137
      · subst h3; norm_num
      · exact absurd (hpz ▸ hp) hzP
      · rw [h137.2]; norm_num
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c hcP hcd _ hne
      dsimp only [β] at hne
      split_ifs at hne with hc3 hcz h137
      · subst hc3
        exact absurd hcd (S4 3 Nat.prime_three (by norm_num) (hnz (by omega)) h3m p hp)
      · exact absurd (hcz ▸ hcP) hzP
      · rw [h137.2] at hcd
        exact absurd hcd (S8 7 (by norm_num) (by norm_num) (hnz (by omega)) (h7kill h137.1) p hp)
      · exact absurd rfl hne
    · refine ⟨?_, ?_, ?_, ?_⟩
      · dsimp only [β]; norm_num
      · dsimp only [β]; split_ifs <;> norm_num
      · dsimp only [β]; split_ifs <;> norm_num
      · dsimp only [β]; split_ifs <;> norm_num
    · have hβ3 : β 3 ≤ 56 / 41 := by dsimp only [β]; norm_num
      have hβ7 : β 7 = (if z = 7 then 1 else if z = 13 then 8 / 7 else 8 / 6) := by
        dsimp only [β]
        by_cases h7 : z = 7
        · subst h7; norm_num
        · by_cases h13 : z = 13
          · subst h13; norm_num
          · simp only [show (7 : ℕ) ≠ 3 by norm_num, h7, Ne.symm h7, h13, false_and, ↓reduceIte]; norm_num
      have hβ31 : β 31 = (if z = 31 then 1 else 32 / 30) := by
        dsimp only [β]
        by_cases h31 : z = 31
        · subst h31; norm_num
        · simp only [show (31 : ℕ) ≠ 3 by norm_num, h31, Ne.symm h31, show (31 : ℕ) ≠ 7 by norm_num, and_false, ↓reduceIte]; norm_num
      have hβ127 : β 127 = (if z = 127 then 1 else 128 / 126) := by
        dsimp only [β]
        by_cases h127 : z = 127
        · subst h127; norm_num
        · simp only [show (127 : ℕ) ≠ 3 by norm_num, h127, Ne.symm h127, show (127 : ℕ) ≠ 7 by norm_num, and_false, ↓reduceIte]; norm_num
      rw [hβ7, hβ31, hβ127]
      have hpos : (0 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ e0) *
          ((if z = 7 then 1 else if z = 13 then 8 / 7 else 8 / 6) *
            (if z = 31 then 1 else 32 / 30) * (if z = 127 then 1 else 128 / 126) *
            (2048 / 2047) * ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
              (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) * ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)))) := by
        have hz7q : (7 : ℚ) ≤ z := by exact_mod_cast hz7
        have hSpos : (0 : ℚ) ≤ ∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
          Finset.prod_nonneg fun q hq => B_nonneg (by have := hS_gt1 q hq; omega)
        have h64p : (0 : ℚ) ≤ ((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2) := by
          push_cast; exact div_nonneg (by nlinarith) (by nlinarith)
        have hz2p : (0 : ℚ) ≤ (z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3) :=
          div_nonneg (by nlinarith) (by nlinarith)
        split_ifs <;> positivity
      have hmul := mul_le_mul_of_nonneg_right hβ3 hpos
      have heq1 : β 3 * ((1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ e0) *
          ((if z = 7 then 1 else if z = 13 then 8 / 7 else 8 / 6) *
            (if z = 31 then 1 else 32 / 30) * (if z = 127 then 1 else 128 / 126) *
            (2048 / 2047) * ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
              (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) * ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3))))) =
          (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ e0) *
          ((β 3 * (if z = 7 then 1 else if z = 13 then 8 / 7 else 8 / 6) *
            (if z = 31 then 1 else 32 / 30) * (if z = 127 then 1 else 128 / 126)) *
            (2048 / 2047) * ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
              (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) * ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)))) := by ring
      have heq2 : (56 / 41 : ℚ) * ((1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ e0) *
          ((if z = 7 then 1 else if z = 13 then 8 / 7 else 8 / 6) *
            (if z = 31 then 1 else 32 / 30) * (if z = 127 then 1 else 128 / 126) *
            (2048 / 2047) * ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
              (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) * ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3))))) =
          (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ e0) *
          (((56 / 41 : ℚ) * (if z = 7 then 1 else if z = 13 then 8 / 7 else 8 / 6) *
            (if z = 31 then 1 else 32 / 30) * (if z = 127 then 1 else 128 / 126)) *
            (2048 / 2047) * ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
              (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) * ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)))) := by ring
      linarith
  · obtain ⟨p0, hp0P, hp0d, hp03, hp041⟩ := exists_p0_ge_41 hP hz hz3 (by omega) E hm4
    have hp0p : p0.Prime := (hP p0 hp0P).1
    have hp02 : p0 ≠ 2 := (hP p0 hp0P).2
    have hne3 : p0 ≠ 3 := by omega
    have hnez : p0 ≠ z := by omega
    have hne7 : p0 ≠ 7 := by omega
    have hne31 : p0 ≠ 31 := by omega
    have hne127 : p0 ≠ 127 := by omega
    let β : ℕ → ℚ := fun p =>
      if p = 3 then 56 / 41
      else if p = z then 1
      else if z = 13 ∧ p = 7 then 8 / 7
      else if p = p0 then 1 + 1 / (p0 : ℚ)
      else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    have hSβ : ∀ q ∈ S, β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
      dsimp only [β]
      have hq3 : q ≠ 3 := fun h => hS_ne3 (h ▸ hq)
      have hqz : q ≠ z := fun h => hS_nez (h ▸ hq)
      have hq7 : q ≠ 7 := fun h => hS_ne7 (h ▸ hq)
      have hqp0 : q ≠ p0 := fun h => hS_mod3 q hq (h ▸ hp03)
      simp only [hq3, hqz, hq7, hqp0, and_false, ↓reduceIte]
    refine graham_contra (e0 := e0) hP hz hm he E β ?_ ?_ ?_
      (fun L hLp hLz hLβ => by
        have h := zleaf_k6_bound hz hz7 S hS hLp hLz hLβ (fun q hq => by
          rw [hSβ q hq]
          have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hS_gt1 q hq
          rw [le_div_iff₀ (by linarith)]; linarith)
        simpa only [Finset.prod_congr rfl hSβ] using h) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3 hpz h137 hp0
      · subst h3; norm_num
      · exact absurd (hpz ▸ hp) hzP
      · rw [h137.2]; norm_num
      · subst hp0; exact ⟨le_rfl, one_add_le_B hp0p.two_le⟩
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c hcP hcd _ hne
      dsimp only [β] at hne
      split_ifs at hne with hc3 hcz h137 hcp0
      · subst hc3
        have hpeq : p = p0 := S3 3 Nat.prime_three (by norm_num) (hnz (by omega)) p hp p0 hp0P hcd (by omega)
        rw [hpeq]
        dsimp only [β]
        simp only [hne3, hnez, hne7, and_false, ↓reduceIte]
        have hp0q : (41 : ℚ) ≤ (p0 : ℚ) := by exact_mod_cast hp041
        have hdiv : (1 : ℚ) / (p0 : ℚ) ≤ 1 / 41 := one_div_le_one_div_of_le (by norm_num) hp0q
        linarith
      · exact absurd (hcz ▸ hcP) hzP
      · rw [h137.2] at hcd
        exact absurd hcd (S8 7 (by norm_num) (by norm_num) (hnz (by omega)) (h7kill h137.1) p hp)
      · rw [hcp0] at hcd
        exact absurd hcd (S4 p0 hp0p hp02 (hnz hnez) hp0d p hp)
      · exact absurd rfl hne
    · refine ⟨?_, ?_, ?_, ?_⟩
      · dsimp only [β]; norm_num
      · dsimp only [β]
        by_cases h7 : z = 7
        · subst h7; norm_num
        · by_cases h13 : z = 13
          · subst h13; norm_num
          · simp only [show (7 : ℕ) ≠ 3 by norm_num, Ne.symm h7, h13, false_and, hne7.symm, ↓reduceIte]; norm_num
      · dsimp only [β]
        by_cases h31 : z = 31
        · subst h31; norm_num
        · simp only [show (31 : ℕ) ≠ 3 by norm_num, Ne.symm h31, show (31 : ℕ) ≠ 7 by norm_num, and_false, hne31.symm, ↓reduceIte]; norm_num
      · dsimp only [β]
        by_cases h127 : z = 127
        · subst h127; norm_num
        · simp only [show (127 : ℕ) ≠ 3 by norm_num, Ne.symm h127, show (127 : ℕ) ≠ 7 by norm_num, and_false, hne127.symm, ↓reduceIte]; norm_num
    · have hβ3 : β 3 = 56 / 41 := by dsimp only [β]; norm_num
      have hβ7 : β 7 = (if z = 7 then 1 else if z = 13 then 8 / 7 else 8 / 6) := by
        dsimp only [β]
        by_cases h7 : z = 7
        · subst h7; norm_num
        · by_cases h13 : z = 13
          · subst h13; norm_num
          · simp only [show (7 : ℕ) ≠ 3 by norm_num, h7, Ne.symm h7, h13, false_and, hne7.symm, ↓reduceIte]; norm_num
      have hβ31 : β 31 = (if z = 31 then 1 else 32 / 30) := by
        dsimp only [β]
        by_cases h31 : z = 31
        · subst h31; norm_num
        · simp only [show (31 : ℕ) ≠ 3 by norm_num, h31, Ne.symm h31, show (31 : ℕ) ≠ 7 by norm_num, and_false, hne31.symm, ↓reduceIte]; norm_num
      have hβ127 : β 127 = (if z = 127 then 1 else 128 / 126) := by
        dsimp only [β]
        by_cases h127 : z = 127
        · subst h127; norm_num
        · simp only [show (127 : ℕ) ≠ 3 by norm_num, h127, Ne.symm h127, show (127 : ℕ) ≠ 7 by norm_num, and_false, hne127.symm, ↓reduceIte]; norm_num
      rw [hβ3, hβ7, hβ31, hβ127]
      exact hnum

-- Section 4. Parent-exclusion helpers and m = 2 mod 4 kills for all 16 surviving primes.

private theorem two_mul_dvd_of_odd {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : c % 2 = 1)
    (hd : c ∣ p + 1) : 2 * c ∣ p + 1 := by
  have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h2 : 2 ∣ p + 1 := by omega
  have hcop : Nat.Coprime 2 c := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hc
  exact hcop.mul_dvd_of_dvd_of_dvd h2 hd

private theorem parent_ge_223_of_c7 {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp13 : p ≠ 13) (hp181 : p ≠ 181) (hz3 : z ≠ 3) (hz5 : z ≠ 5)
    (h7 : 7 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 7 ≤ c')
    (hsq7 : ¬ 7 * 7 ∣ p + 1) : 223 ≤ p := by
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
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk15 : k ≤ 15 := by omega
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 11 ∨ k = 13 := by
    interval_cases k <;> omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp13 (by omega)
  · norm_num [show p = 27 from by omega] at hp
  · norm_num [show p = 55 from by omega] at hp
  · norm_num [show p = 111 from by omega] at hp
  · norm_num [show p = 153 from by omega] at hp
  · exact hp181 (by omega)

private theorem parent_ge_103_of_c13 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h13 : 13 ∣ p + 1) :
    103 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h13
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 25 from by omega] at hp
  · norm_num [show p = 51 from by omega] at hp
  · norm_num [show p = 77 from by omega] at hp

private theorem parent_ge_487_of_c31 {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp61 : p ≠ 61)
    (hz7 : z ≠ 7) (h31 : 31 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 31 ≤ c') :
    487 ≤ p := by
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
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
  · have := hmin 7 (by norm_num) (by norm_num) (hnz hz7.symm) ⟨62, by omega⟩
    omega

private theorem parent_ge_487_of_c61 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h61 : 61 ∣ p + 1) :
    487 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h61
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 121 from by omega] at hp
  · norm_num [show p = 243 from by omega] at hp
  · norm_num [show p = 365 from by omega] at hp

private theorem parent_ge_823_of_c103 {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hz3 : z ≠ 3)
    (h103 : 103 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 103 ≤ c') :
    823 ≤ p := by
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h103
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 205 from by omega] at hp
  · norm_num [show p = 411 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (hnz hz3.symm) ⟨206, by omega⟩
    omega

private theorem parent_ge_1000_of_c127 {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hz3 : z ≠ 3)
    (h127 : 127 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    1000 ≤ p := by
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h127
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 253 from by omega] at hp
  · norm_num [show p = 507 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (hnz hz3.symm) ⟨254, by omega⟩
    omega

private theorem parent_ge_1000_of_c13 {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp103 : p ≠ 103) (hp883 : p ≠ 883)
    (hz3 : z ≠ 3) (hz5 : z ≠ 5) (hz7 : z ≠ 7) (hz11 : z ≠ 11)
    (h13 : 13 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 13 ≤ c')
    (hsq13 : ¬ 13 * 13 ∣ p + 1) : 1000 ≤ p := by
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h13
  have h3m : k % 3 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 3 (by norm_num) (by norm_num) (hnz hz3.symm) ⟨26 * t, by omega⟩
    omega
  have h5m : k % 5 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 5 (by norm_num) (by norm_num) (hnz hz5.symm) ⟨26 * t, by omega⟩
    omega
  have h7m : k % 7 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 7 (by norm_num) (by norm_num) (hnz hz7.symm) ⟨26 * t, by omega⟩
    omega
  have h11m : k % 11 ≠ 0 := fun hm => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hm
    have := hmin 11 (by norm_num) (by norm_num) (hnz hz11.symm) ⟨26 * t, by omega⟩
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

private theorem parent_ge_7927_of_c991 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h991 : 991 ∣ p + 1) :
    7927 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h991
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 1981 from by omega] at hp
  · norm_num [show p = 3963 from by omega] at hp
  · norm_num [show p = 5945 from by omega] at hp

private theorem parent_ge_6583_of_c823_z31 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h823 : 823 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({31} : Finset ℕ) → c' ∣ p + 1 → 823 ≤ c') :
    6583 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h823
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · norm_num [show p = 1645 from by omega] at hp
  · norm_num [show p = 3291 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (by decide) ⟨1646, by omega⟩
    omega

private theorem parent_ge_1441_of_c103_z31 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp823 : p ≠ 823)
    (h103 : 103 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({31} : Finset ℕ) → c' ∣ p + 1 → 103 ≤ c') :
    1441 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h103
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk6 : k ≤ 6 := by omega
  interval_cases k
  · norm_num [show p = 205 from by omega] at hp
  · norm_num [show p = 411 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (by decide) ⟨206, by omega⟩
    omega
  · exact hp823 (by omega)
  · norm_num [show p = 1029 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (by decide) ⟨412, by omega⟩
    omega

private theorem parent_ge_2031_of_c127_z31 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h127 : 127 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({31} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    2031 ≤ p := by
  obtain ⟨k, hk⟩ := two_mul_dvd_of_odd hp hp2 (by norm_num) h127
  by_contra hlt
  have hk1 : 1 ≤ k := by omega
  have hk7 : k ≤ 7 := by omega
  interval_cases k
  · norm_num [show p = 253 from by omega] at hp
  · norm_num [show p = 507 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (by decide) ⟨254, by omega⟩
    omega
  · norm_num [show p = 1015 from by omega] at hp
  · norm_num [show p = 1269 from by omega] at hp
  · have := hmin 3 (by norm_num) (by norm_num) (by decide) ⟨508, by omega⟩
    omega
  · have := hmin 7 (by norm_num) (by norm_num) (by decide) ⟨254, by omega⟩
    omega

-- Fast non-recursive leaf-set membership proofs (avoids decide recursion depth on Nat.Prime).
private theorem hS_z7 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 7 - 1).Prime → 2 ^ k * 7 - 1 ∈ ({13, 223} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _) | norm_num at hp

private theorem hS_z7_j2 : ∀ k ∈ Finset.Icc 1 4, (2 ^ k * 7 ^ 2 - 1).Prime → 2 ^ k * 7 ^ 2 - 1 ∈ ({97} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h4 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z13 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 13 - 1).Prime → 2 ^ k * 13 - 1 ∈ ({103} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z13_j2 : ∀ k ∈ Finset.Icc 1 4, (2 ^ k * 13 ^ 2 - 1).Prime → 2 ^ k * 13 ^ 2 - 1 ∈ ({337} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h4 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z31 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 31 - 1).Prime → 2 ^ k * 31 - 1 ∈ ({61, 991} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _) | norm_num at hp

private theorem hS_z31_j2 : ∀ k ∈ Finset.Icc 1 4, (2 ^ k * 31 ^ 2 - 1).Prime → 2 ^ k * 31 ^ 2 - 1 ∈ ({7687} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h4 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z61 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 61 - 1).Prime → 2 ^ k * 61 - 1 ∈ ({487, 1951} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _) | norm_num at hp

private theorem hS_z103 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 103 - 1).Prime → 2 ^ k * 103 - 1 ∈ ({823} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z127 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 127 - 1).Prime → 2 ^ k * 127 - 1 ∈ (∅ : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> norm_num at hp

private theorem hS_z223 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 223 - 1).Prime → 2 ^ k * 223 - 1 ∈ ({1783} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z433 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 433 - 1).Prime → 2 ^ k * 433 - 1 ∈ ({3463} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z487 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 487 - 1).Prime → 2 ^ k * 487 - 1 ∈ ({15583} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z823 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 823 - 1).Prime → 2 ^ k * 823 - 1 ∈ (∅ : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> norm_num at hp

private theorem hS_z853 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 853 - 1).Prime → 2 ^ k * 853 - 1 ∈ ({6823} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z991 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 991 - 1).Prime → 2 ^ k * 991 - 1 ∈ ({7927} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

private theorem hS_z1663 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 1663 - 1).Prime → 2 ^ k * 1663 - 1 ∈ (∅ : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> norm_num at hp

private theorem hS_z1777 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 1777 - 1).Prime → 2 ^ k * 1777 - 1 ∈ (∅ : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> norm_num at hp

private theorem hS_z1783 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 1783 - 1).Prime → 2 ^ k * 1783 - 1 ∈ (∅ : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> norm_num at hp

private theorem hS_z1951 : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * 1951 - 1).Prime → 2 ^ k * 1951 - 1 ∈ ({15607} : Finset ℕ) := by
  intro k hk hp; have h1 := (Finset.mem_Icc.mp hk).1; have h6 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first | exact Finset.mem_singleton_self _ | norm_num at hp

-- Template A: z in {223, 433, 853, 1777, 1783} with m = 2 mod 4 (pure forced-chain weights).
private theorem kill_mod2_7dvd {m e z : ℕ} {P : Finset ℕ} (S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hz7 : 7 < z) (hm : 20 ≤ m) (he : Odd e)
    (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (h7d : 7 ∣ z + 1)
    (hS : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 ∈ S)
    (hS_ne : ∀ q ∈ S, q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7)
    (hS_gt1 : ∀ q ∈ S, 2 ≤ q)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hnum : (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ 3) *
      (((8 / 5 : ℚ) * (8 / 7) * (32 / 30) * (128 / 126)) * (2048 / 2047) *
        ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) *
          ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)))) < 2) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, S4, -, -, -, S8⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by omega)) h5m
  have h7K : 7 ∣ 1 + z ^ e := h7d.trans (dvd_one_add_pow_of_odd he)
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 7 then 8 / 7
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have hSβ : ∀ q ∈ S, β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
    dsimp only [β]
    obtain ⟨h3, h5, h7⟩ := hS_ne q hq
    simp only [h3, h5, h7, ↓reduceIte]
  refine graham_contra (e0 := 3) hP hz hm he3 E β ?_ ?_ ?_
    (fun L hLp hLz hLβ => by
      have h := zleaf_k6_bound hz (by omega) S hS hLp hLz hLβ (fun q hq => by
        rw [hSβ q hq]
        have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hS_gt1 q hq
        rw [le_div_iff₀ (by linarith)]; linarith)
      simpa only [Finset.prod_congr rfl hSβ] using h) ?_
  · intro p hp
    dsimp only [β]
    split_ifs with h3 h5 h7
    · subst h3; norm_num
    · subst h5; norm_num
    · subst h7; norm_num
    · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c _ hcd _ hne
    dsimp only [β] at hne
    split_ifs at hne with hc3 hc5 hc7
    · subst hc3
      have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by omega)) p hp 5 h5P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc5
      exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by omega)) h5m p hp)
    · subst hc7
      exact absurd hcd (S8 7 (by norm_num) (by norm_num) (hnz (by omega)) h7K p hp)
    · exact absurd rfl hne
  · dsimp only [β]; norm_num
  · have h3 : β 3 = 8 / 5 := by dsimp only [β]; norm_num
    have h7 : β 7 = 8 / 7 := by dsimp only [β]; norm_num
    have h31 : β 31 = 32 / 30 := by dsimp only [β]; norm_num
    have h127 : β 127 = 128 / 126 := by dsimp only [β]; norm_num
    rw [h3, h7, h31, h127]; exact hnum

private theorem kill_mod2_z1783 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hm : 20 ≤ m) (he : Odd e) (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 1783 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1783 ^ e * ∏ p ∈ P, p) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 1783) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 1783 → c ∉ ({1783} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, S4, -, -, S7, S8⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  have h223K : 223 ∣ 1 + 1783 ^ e := Dvd.dvd.trans (by norm_num : 223 ∣ 1783 + 1) (dvd_one_add_pow_of_odd he)
  have h223P : 223 ∈ P := S7 223 (by norm_num) (by norm_num) (hnz (by norm_num)) h223K
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 223 then 224 / 223
    else if p = 7 then (8 / 7) * (224 / 223)
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  refine graham_contra (e0 := 3) hP (by norm_num) hm he3 E β ?_ ?_ ?_
    (fun L hLp hLz hLβ => by
      have h := zleaf_k6_bound (z := 1783) (by norm_num) (by norm_num) ∅ hS_z1783 hLp hLz hLβ (by simp)
      simpa using h) ?_
  · intro p hp
    dsimp only [β]
    split_ifs with h3 h5 h223 h7
    · subst h3; norm_num
    · subst h5; norm_num
    · subst h223; norm_num
    · subst h7; norm_num
    · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c _ hcd _ hne
    dsimp only [β] at hne
    split_ifs at hne with hc3 hc5 hc223 hc7
    · subst hc3
      have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc5
      exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
    · subst hc223
      exact absurd hcd (S8 223 (by norm_num) (by norm_num) (hnz (by norm_num)) h223K p hp)
    · subst hc7
      have hpeq : p = 223 := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 223 h223P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · exact absurd rfl hne
  · dsimp only [β]; norm_num
  · dsimp only [β]; norm_num

-- Template B: z in {61, 487, 991, 1951} with m = 2 mod 4 (31 in chain -> 13 not in P -> beta 7 = (8/7)B(223)).
private theorem kill_mod2_31chain {m e z : ℕ} {P : Finset ℕ} (S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hz61 : 61 ≤ z) (hm : 20 ≤ m) (he : Odd e)
    (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (h31src : (31 ∣ z + 1) ∨ (61 ∣ z + 1 ∧ z ≠ 61))
    (hS : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 ∈ S)
    (hS_ne : ∀ q ∈ S, q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 31 ∧ q ≠ 61)
    (hS_gt1 : ∀ q ∈ S, 2 ≤ q)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hnum : (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ 3) *
      (((8 / 5 : ℚ) * ((8 / 7) * (224 / 222)) * (64 / 61) * (128 / 126)) * (2048 / 2047) *
        ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) *
          ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)))) < 2) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, S6, S7, S8⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by omega)) h5m
  have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by omega)) 5 h5P (by norm_num)
  have h31P : 31 ∈ P := by
    rcases h31src with h31d | ⟨h61d, hne61⟩
    · exact S7 31 (by norm_num) (by norm_num) (hnz (by omega)) (h31d.trans (dvd_one_add_pow_of_odd he))
    · have h61P : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz hne61.symm)
        (h61d.trans (dvd_one_add_pow_of_odd he))
      exact S1 31 (by norm_num) (by norm_num) (hnz (by omega)) 61 h61P (by norm_num)
  have h13P : 13 ∉ P := fun h13 => by
    have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by omega)) 13 h13 (by norm_num)
    exact weight_kill hP E (L := [3, 5, 7, 13, 31]) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
  have h181P : 181 ∉ P := fun h181 =>
    h13P (S1 13 (by norm_num) (by norm_num) (hnz (by omega)) 181 h181 (by norm_num))
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 7 then (8 / 7) * (224 / 222)
    else if p = 31 then 64 / 61
    else if p = 61 then (if 31 ∣ z + 1 then ((61 : ℚ) + 1) / ((61 : ℚ) - 1) else 62 / 61)
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have hSβ : ∀ q ∈ S, β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
    dsimp only [β]
    obtain ⟨h3, h5, h7, h31, h61⟩ := hS_ne q hq
    simp only [h3, h5, h7, h31, h61, ↓reduceIte]
  refine graham_contra (e0 := 3) hP hz hm he3 E β ?_ ?_ ?_
    (fun L hLp hLz hLβ => by
      have h := zleaf_k6_bound hz (by omega) S hS hLp hLz hLβ (fun q hq => by
        rw [hSβ q hq]
        have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hS_gt1 q hq
        rw [le_div_iff₀ (by linarith)]; linarith)
      simpa only [Finset.prod_congr rfl hSβ] using h) ?_
  · intro p hp
    dsimp only [β]
    split_ifs with h3 h5 h7 h31 h61 h31d
    · subst h3; norm_num
    · subst h5; norm_num
    · subst h7; norm_num
    · subst h31; norm_num
    · subst h61; norm_num
    · subst h61; norm_num
    · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c _ hcd hmin hne
    have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
      dsimp only [β]
      split_ifs with h3 h5 h7 h31 h61 h31d
      · subst h3; norm_num
      · subst h5; norm_num
      · subst h7; norm_num
      · subst h31; norm_num
      · subst h61; norm_num
      · subst h61; norm_num
      · exact le_rfl
    dsimp only [β] at hne
    split_ifs at hne with hc3 hc5 hc7 hc31 hc61 h31d
    · subst hc3
      have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by omega)) p hp 5 h5P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc5
      exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by omega)) h5m p hp)
    · subst hc7
      have hp13 : p ≠ 13 := fun h => h13P (h ▸ hp)
      have hp181 : p ≠ 181 := fun h => h181P (h ▸ hp)
      have hsq7 : ¬ 7 * 7 ∣ p + 1 := S6 7 (by norm_num) (by norm_num) (hnz (by omega)) p hp
      have hp223 : 223 ≤ p := parent_ge_223_of_c7 (hP p hp).1 (hP p hp).2 hp13 hp181
        (by omega) (by omega) hcd hmin hsq7
      have hle : β p ≤ 224 / 222 := hBp.trans ((B_anti (by norm_num : 2 ≤ 223) hp223).trans (by norm_num))
      have hβc : β 7 = (8 / 7) * (224 / 222) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (7 : ℚ)) * β p ≤ (1 + 1 / (7 : ℚ)) * (224 / 222) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    · subst hc31
      rcases h31src with h31d | ⟨h61d, hne61⟩
      · exact absurd hcd (S8 31 (by norm_num) (by norm_num) (hnz (by omega))
          (h31d.trans (dvd_one_add_pow_of_odd he)) p hp)
      · have h61P : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz hne61.symm)
          (h61d.trans (dvd_one_add_pow_of_odd he))
        have hpeq : p = 61 := S3 31 (by norm_num) (by norm_num) (hnz (by omega)) p hp 61 h61P hcd (by norm_num)
        rw [hpeq]
        have hnd31 : ¬ 31 ∣ z + 1 := fun h31d =>
          S8 31 (by norm_num) (by norm_num) (hnz (by omega)) (h31d.trans (dvd_one_add_pow_of_odd he)) 61 h61P (by norm_num)
        dsimp only [β]
        simp only [hnd31, ↓reduceIte]
        norm_num
    · subst hc61
      norm_num at hne
    · subst hc61
      rcases h31src with h31d' | ⟨h61d, hne61⟩
      · exact absurd h31d' h31d
      · exact absurd hcd (S8 61 (by norm_num) (by norm_num) (hnz hne61.symm)
          (h61d.trans (dvd_one_add_pow_of_odd he)) p hp)
    · exact absurd rfl hne
  · dsimp only [β]; norm_num
  · have h3 : β 3 = 8 / 5 := by dsimp only [β]; norm_num
    have h7 : β 7 = (8 / 7) * (224 / 222) := by dsimp only [β]; norm_num
    have h31 : β 31 = 64 / 61 := by dsimp only [β]; norm_num
    have h127 : β 127 = 128 / 126 := by dsimp only [β]; norm_num
    rw [h3, h7, h31, h127]; exact hnum

-- Template C: z in {103, 823, 1663} with m = 2 mod 4 (13 in chain -> 31 not in P).
private theorem kill_mod2_13dvd {m e z : ℕ} {P : Finset ℕ} (S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hz103 : 103 ≤ z) (hm : 20 ≤ m) (he : Odd e)
    (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (h13d : 13 ∣ z + 1)
    (hS : ∀ k ∈ Finset.Icc 1 6, (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 ∈ S)
    (hS_ne : ∀ q ∈ S, q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 ∧ q ≠ 31 ∧ q ≠ 127)
    (hS_gt1 : ∀ q ∈ S, 2 ≤ q)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hnum : (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ 3) *
      (((8 / 5 : ℚ) * (16 / 13) * 1 * ((128 / 127) * (1001 / 999))) * (2048 / 2047) *
        ((∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (((64 * z : ℕ) : ℚ) / ((64 * z : ℕ) - 2)) *
          ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)))) < 2) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, -, S7, S8⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by omega)) h5m
  have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by omega)) 5 h5P (by norm_num)
  have h13K : 13 ∣ 1 + z ^ e := h13d.trans (dvd_one_add_pow_of_odd he)
  have h13P : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by omega)) h13K
  have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by omega)) 13 h13P (by norm_num)
  have h31P : 31 ∉ P := fun h31 =>
    weight_kill hP E (L := [3, 5, 7, 13, 31]) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 13 then 14 / 13
    else if p = 7 then 16 / 13
    else if p = 31 then 1
    else if p = 127 then (128 / 127) * (1001 / 999)
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have hSβ : ∀ q ∈ S, β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
    dsimp only [β]
    obtain ⟨h3, h5, h7, h13, h31, h127⟩ := hS_ne q hq
    simp only [h3, h5, h7, h13, h31, h127, ↓reduceIte]
  refine graham_contra (e0 := 3) hP hz hm he3 E β ?_ ?_ ?_
    (fun L hLp hLz hLβ => by
      have h := zleaf_k6_bound hz (by omega) S hS hLp hLz hLβ (fun q hq => by
        rw [hSβ q hq]
        have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hS_gt1 q hq
        rw [le_div_iff₀ (by linarith)]; linarith)
      simpa only [Finset.prod_congr rfl hSβ] using h) ?_
  · intro p hp
    dsimp only [β]
    split_ifs with h3 h5 h13 h7 h31 h127
    · subst h3; norm_num
    · subst h5; norm_num
    · subst h13; norm_num
    · subst h7; norm_num
    · exact absurd (h31 ▸ hp) h31P
    · subst h127; norm_num
    · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c hcP hcd hmin hne
    have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
      dsimp only [β]
      split_ifs with h3 h5 h13 h7 h31 h127
      · subst h3; norm_num
      · subst h5; norm_num
      · subst h13; norm_num
      · subst h7; norm_num
      · exact absurd (h31 ▸ hp) h31P
      · subst h127; norm_num
      · exact le_rfl
    dsimp only [β] at hne
    split_ifs at hne with hc3 hc5 hc13 hc7 hc31 hc127
    · subst hc3
      have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by omega)) p hp 5 h5P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc5
      exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by omega)) h5m p hp)
    · subst hc13
      exact absurd hcd (S8 13 (by norm_num) (by norm_num) (hnz (by omega)) h13K p hp)
    · subst hc7
      have hpeq : p = 13 := S3 7 (by norm_num) (by norm_num) (hnz (by omega)) p hp 13 h13P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · exact absurd (hc31 ▸ hcP) h31P
    · subst hc127
      have hp1000 : 1000 ≤ p := parent_ge_1000_of_c127 (hP p hp).1 (hP p hp).2 (by omega) hcd hmin
      have hle : β p ≤ 1001 / 999 := hBp.trans ((B_anti (by norm_num : 2 ≤ 1000) hp1000).trans (by norm_num))
      have hβc : β 127 = (128 / 127) * (1001 / 999) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (127 : ℚ)) * β p ≤ (1 + 1 / (127 : ℚ)) * (1001 / 999) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    · exact absurd rfl hne
  · dsimp only [β]; norm_num
  · have h3 : β 3 = 8 / 5 := by dsimp only [β]; norm_num
    have h7 : β 7 = 16 / 13 := by dsimp only [β]; norm_num
    have h31 : β 31 = 1 := by dsimp only [β]; norm_num
    have h127 : β 127 = (128 / 127) * (1001 / 999) := by dsimp only [β]; norm_num
    rw [h3, h7, h31, h127]; exact hnum

private theorem kill_mod2_z823 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hm : 20 ≤ m) (he : Odd e) (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 823 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 823 ^ e * ∏ p ∈ P, p) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 823) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 823 → c ∉ ({823} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, -, S7, S8⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 5 h5P (by norm_num)
  have h103K : 103 ∣ 1 + 823 ^ e := Dvd.dvd.trans (by norm_num : 103 ∣ 823 + 1) (dvd_one_add_pow_of_odd he)
  have h103P : 103 ∈ P := S7 103 (by norm_num) (by norm_num) (hnz (by norm_num)) h103K
  have h13P : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 h103P (by norm_num)
  have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 h13P (by norm_num)
  have h31P : 31 ∉ P := fun h31 =>
    weight_kill hP E (L := [3, 5, 7, 13, 31]) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
  have h127P : 127 ∉ P := fun h127 =>
    weight_kill hP E (L := [3, 5, 7, 13, 103, 127]) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 103 then 104 / 103
    else if p = 13 then (14 / 13) * (104 / 103)
    else if p = 7 then (8 / 7) * ((14 / 13) * (104 / 103))
    else if p = 31 then 1
    else if p = 127 then 1
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  refine graham_contra (e0 := 3) hP (by norm_num) hm he3 E β ?_ ?_ ?_
    (fun L hLp hLz hLβ => by
      have h := zleaf_k6_bound (z := 823) (by norm_num) (by norm_num) ∅ hS_z823 hLp hLz hLβ (by simp)
      simpa using h) ?_
  · intro p hp
    dsimp only [β]
    split_ifs with h3 h5 h103 h13 h7 h31 h127
    · subst h3; norm_num
    · subst h5; norm_num
    · subst h103; norm_num
    · subst h13; norm_num
    · subst h7; norm_num
    · exact absurd (h31 ▸ hp) h31P
    · exact absurd (h127 ▸ hp) h127P
    · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c hcP hcd _ hne
    dsimp only [β] at hne
    split_ifs at hne with hc3 hc5 hc103 hc13 hc7 hc31 hc127
    · subst hc3
      have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc5
      exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
    · subst hc103
      exact absurd hcd (S8 103 (by norm_num) (by norm_num) (hnz (by norm_num)) h103K p hp)
    · subst hc13
      have hpeq : p = 103 := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 103 h103P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc7
      have hpeq : p = 13 := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 13 h13P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · exact absurd (hc31 ▸ hcP) h31P
    · exact absurd (hc127 ▸ hcP) h127P
    · exact absurd rfl hne
  · dsimp only [β]; norm_num
  · dsimp only [β]; norm_num

-- Template D: z = 127 with m = 2 mod 4.
private theorem kill_mod2_z127 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h127P : 127 ∉ P) (hm : 20 ≤ m) (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 127 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 127 ^ e * ∏ p ∈ P, p) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 127) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 127 → c ∉ ({127} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, S6, -, -⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 5 h5P (by norm_num)
  by_cases h13P : 13 ∈ P
  · have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 h13P (by norm_num)
    have h31P : 31 ∉ P := fun h31 =>
      weight_kill hP E (L := [3, 5, 7, 13, 31]) (by decide) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
    by_cases h103P : 103 ∈ P
    · let β : ℕ → ℚ := fun p =>
        if p = 3 then 8 / 5
        else if p = 5 then 6 / 5
        else if p = 31 then 1
        else if p = 127 then 1
        else if p = 103 then (104 / 103) * (824 / 822)
        else if p = 13 then (14 / 13) * ((104 / 103) * (824 / 822))
        else if p = 7 then (8 / 7) * ((14 / 13) * ((104 / 103) * (824 / 822)))
        else ((p : ℚ) + 1) / ((p : ℚ) - 1)
      refine graham_contra (e0 := 3) hP (by norm_num) hm he3 E β ?_ ?_ ?_
        (fun L hLp hLz hLβ => by
          have h := zleaf_k6_bound (z := 127) (by norm_num) (by norm_num) ∅ hS_z127 hLp hLz hLβ (by simp)
          simpa using h) ?_
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
          have hp823 : 823 ≤ p := parent_ge_823_of_c103 (hP p hp).1 (hP p hp).2 (by norm_num) hcd hmin
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
    · have h883P : 883 ∉ P := fun h883 => by
        have h17P : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 883 h883 (by norm_num)
        exact S6 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 17 h17P (by norm_num)
      let β : ℕ → ℚ := fun p =>
        if p = 3 then 8 / 5
        else if p = 5 then 6 / 5
        else if p = 31 then 1
        else if p = 127 then 1
        else if p = 13 then (14 / 13) * (1001 / 999)
        else if p = 7 then (8 / 7) * ((14 / 13) * (1001 / 999))
        else ((p : ℚ) + 1) / ((p : ℚ) - 1)
      refine graham_contra (e0 := 3) hP (by norm_num) hm he3 E β ?_ ?_ ?_
        (fun L hLp hLz hLβ => by
          have h := zleaf_k6_bound (z := 127) (by norm_num) (by norm_num) ∅ hS_z127 hLp hLz hLβ (by simp)
          simpa using h) ?_
      · intro p hp
        dsimp only [β]
        split_ifs with h3 h5 h31 h127 h13 h7
        · subst h3; norm_num
        · subst h5; norm_num
        · exact absurd (h31 ▸ hp) h31P
        · exact absurd (h127 ▸ hp) h127P
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
          · exact absurd (h127 ▸ hp) h127P
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
        · exact absurd (hc127 ▸ hcP) h127P
        · subst hc13
          have hp103 : p ≠ 103 := fun h => h103P (h ▸ hp)
          have hp883 : p ≠ 883 := fun h => h883P (h ▸ hp)
          have hsq13 : ¬ 13 * 13 ∣ p + 1 := S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
          have hp1000 : 1000 ≤ p := parent_ge_1000_of_c13 (hP p hp).1 (hP p hp).2 hp103 hp883
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcd hmin hsq13
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
  · have h181P : 181 ∉ P := fun h181 =>
      h13P (S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 h181 (by norm_num))
    let β : ℕ → ℚ := fun p =>
      if p = 3 then 8 / 5
      else if p = 5 then 6 / 5
      else if p = 127 then 1
      else if p = 7 then (8 / 7) * (224 / 222)
      else if p = 61 then (62 / 61) * (488 / 486)
      else if p = 31 then (32 / 31) * ((62 / 61) * (488 / 486))
      else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    refine graham_contra (e0 := 3) hP (by norm_num) hm he3 E β ?_ ?_ ?_
      (fun L hLp hLz hLβ => by
        have h := zleaf_k6_bound (z := 127) (by norm_num) (by norm_num) ∅ hS_z127 hLp hLz hLβ (by simp)
        simpa using h) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3 h5 h127 h7 h61 h31
      · subst h3; norm_num
      · subst h5; norm_num
      · exact absurd (h127 ▸ hp) h127P
      · subst h7; norm_num
      · subst h61; norm_num
      · subst h31; norm_num
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c hcP hcd hmin hne
      have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
        dsimp only [β]
        split_ifs with h3 h5 h127 h7 h61 h31
        · subst h3; norm_num
        · subst h5; norm_num
        · exact absurd (h127 ▸ hp) h127P
        · subst h7; norm_num
        · subst h61; norm_num
        · subst h31; norm_num
        · exact le_rfl
      dsimp only [β] at hne
      split_ifs at hne with hc3 hc5 hc127 hc7 hc61 hc31
      · subst hc3
        have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
        rw [hpeq]; dsimp only [β]; norm_num
      · subst hc5
        exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
      · exact absurd (hc127 ▸ hcP) h127P
      · subst hc7
        have hp13 : p ≠ 13 := fun h => h13P (h ▸ hp)
        have hp181 : p ≠ 181 := fun h => h181P (h ▸ hp)
        have hsq7 : ¬ 7 * 7 ∣ p + 1 := S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
        have hp223 : 223 ≤ p := parent_ge_223_of_c7 (hP p hp).1 (hP p hp).2 hp13 hp181
          (by norm_num) (by norm_num) hcd hmin hsq7
        have hle : β p ≤ 224 / 222 := hBp.trans ((B_anti (by norm_num : 2 ≤ 223) hp223).trans (by norm_num))
        have hβc : β 7 = (8 / 7) * (224 / 222) := by dsimp only [β]; norm_num
        rw [hβc]
        have : (1 + 1 / (7 : ℚ)) * β p ≤ (1 + 1 / (7 : ℚ)) * (224 / 222) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith
      · subst hc61
        have hp487 : 487 ≤ p := parent_ge_487_of_c61 (hP p hp).1 (hP p hp).2 hcd
        have hle : β p ≤ 488 / 486 := hBp.trans ((B_anti (by norm_num : 2 ≤ 487) hp487).trans (by norm_num))
        have hβc : β 61 = (62 / 61) * (488 / 486) := by dsimp only [β]; norm_num
        rw [hβc]
        have : (1 + 1 / (61 : ℚ)) * β p ≤ (1 + 1 / (61 : ℚ)) * (488 / 486) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith
      · subst hc31
        by_cases hp61 : p = 61
        · rw [hp61]; dsimp only [β]; norm_num
        · have hp487 : 487 ≤ p := parent_ge_487_of_c31 (hP p hp).1 (hP p hp).2 hp61 (by norm_num) hcd hmin
          have hle : β p ≤ 488 / 486 := hBp.trans ((B_anti (by norm_num : 2 ≤ 487) hp487).trans (by norm_num))
          have hβc : β 31 = (32 / 31) * ((62 / 61) * (488 / 486)) := by dsimp only [β]; norm_num
          rw [hβc]
          have : (1 + 1 / (31 : ℚ)) * β p ≤ (1 + 1 / (31 : ℚ)) * (488 / 486) :=
            mul_le_mul_of_nonneg_left hle (by norm_num)
          linarith
      · exact absurd rfl hne
    · dsimp only [β]; norm_num
    · dsimp only [β]; norm_num

-- Template E: z in {13, 31, 7} with m = 2 mod 4 (using zleaf_k6_j2_bound).
private theorem kill_mod2_z13 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hm : 20 ≤ m) (he : Odd e) (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 13 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 13 ^ e * ∏ p ∈ P, p) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 13) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 13 → c ∉ ({13} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, S4, -, -, -, S8⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  have h7K : 7 ∣ 1 + 13 ^ e := Dvd.dvd.trans (by norm_num : 7 ∣ 13 + 1) (dvd_one_add_pow_of_odd he)
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 7 then 8 / 7
    else if p = 61 then (62 / 61) * (488 / 486)
    else if p = 31 then (32 / 31) * ((62 / 61) * (488 / 486))
    else if p = 103 then (104 / 103) * (824 / 822)
    else if p = 127 then (128 / 127) * (1001 / 999)
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  refine graham_contra (e0 := 3) hP (by norm_num) hm he3 E β ?_ ?_ ?_
    (fun L hLp hLz hLβ => by
      have h := zleaf_k6_j2_bound (z := 13) (by norm_num) (by norm_num) {103} {337}
        hS_z13 hS_z13_j2 hLp hLz hLβ
        (fun q hq => by rw [Finset.mem_singleton.mp hq]; dsimp only [β]; norm_num)
        (fun q hq => by rw [Finset.mem_singleton.mp hq]; dsimp only [β]; norm_num)
      simpa [β] using h) ?_
  · intro p hp
    dsimp only [β]
    split_ifs with h3 h5 h7 h61 h31 h103 h127
    · subst h3; norm_num
    · subst h5; norm_num
    · subst h7; norm_num
    · subst h61; norm_num
    · subst h31; norm_num
    · subst h103; norm_num
    · subst h127; norm_num
    · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c _ hcd hmin hne
    have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
      dsimp only [β]
      split_ifs with h3 h5 h7 h61 h31 h103 h127
      · subst h3; norm_num
      · subst h5; norm_num
      · subst h7; norm_num
      · subst h61; norm_num
      · subst h31; norm_num
      · subst h103; norm_num
      · subst h127; norm_num
      · exact le_rfl
    dsimp only [β] at hne
    split_ifs at hne with hc3 hc5 hc7 hc61 hc31 hc103 hc127
    · subst hc3
      have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    · subst hc5
      exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
    · subst hc7
      exact absurd hcd (S8 7 (by norm_num) (by norm_num) (hnz (by norm_num)) h7K p hp)
    · subst hc61
      have hp487 : 487 ≤ p := parent_ge_487_of_c61 (hP p hp).1 (hP p hp).2 hcd
      have hle : β p ≤ 488 / 486 := hBp.trans ((B_anti (by norm_num : 2 ≤ 487) hp487).trans (by norm_num))
      have hβc : β 61 = (62 / 61) * (488 / 486) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (61 : ℚ)) * β p ≤ (1 + 1 / (61 : ℚ)) * (488 / 486) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    · subst hc31
      by_cases hp61 : p = 61
      · rw [hp61]; dsimp only [β]; norm_num
      · have hp487 : 487 ≤ p := parent_ge_487_of_c31 (hP p hp).1 (hP p hp).2 hp61 (by norm_num) hcd hmin
        have hle : β p ≤ 488 / 486 := hBp.trans ((B_anti (by norm_num : 2 ≤ 487) hp487).trans (by norm_num))
        have hβc : β 31 = (32 / 31) * ((62 / 61) * (488 / 486)) := by dsimp only [β]; norm_num
        rw [hβc]
        have : (1 + 1 / (31 : ℚ)) * β p ≤ (1 + 1 / (31 : ℚ)) * (488 / 486) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith
    · subst hc103
      have hp823 : 823 ≤ p := parent_ge_823_of_c103 (hP p hp).1 (hP p hp).2 (by norm_num) hcd hmin
      have hle : β p ≤ 824 / 822 := hBp.trans ((B_anti (by norm_num : 2 ≤ 823) hp823).trans (by norm_num))
      have hβc : β 103 = (104 / 103) * (824 / 822) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (103 : ℚ)) * β p ≤ (1 + 1 / (103 : ℚ)) * (824 / 822) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    · subst hc127
      have hp1000 : 1000 ≤ p := parent_ge_1000_of_c127 (hP p hp).1 (hP p hp).2 (by norm_num) hcd hmin
      have hle : β p ≤ 1001 / 999 := hBp.trans ((B_anti (by norm_num : 2 ≤ 1000) hp1000).trans (by norm_num))
      have hβc : β 127 = (128 / 127) * (1001 / 999) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (127 : ℚ)) * β p ≤ (1 + 1 / (127 : ℚ)) * (1001 / 999) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    · exact absurd rfl hne
  · dsimp only [β]; norm_num
  · dsimp only [β]; norm_num

private theorem kill_mod2_z31_13in_103in {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h31P : 31 ∉ P) (h13P : 13 ∈ P) (h103P : 103 ∈ P) (hm : 20 ≤ m) (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 31 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 31 ^ e * ∏ p ∈ P, p) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 31) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 31 → c ∉ ({31} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, -, -, -⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 5 h5P (by norm_num)
  have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 h13P (by norm_num)
  have h61P : 61 ∉ P := fun h61 =>
    weight_kill hP E (L := [3, 5, 7, 13, 61]) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
  have h127P : 127 ∉ P := fun h127 =>
    weight_kill hP E (L := [3, 5, 7, 13, 103, 127]) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 31 then 1
    else if p = 61 then 1
    else if p = 127 then 1
    else if p = 991 then (992 / 991) * (7928 / 7926)
    else if p = 823 then (824 / 823) * (6584 / 6582)
    else if p = 103 then (104 / 103) * ((824 / 823) * (6584 / 6582))
    else if p = 13 then (14 / 13) * ((104 / 103) * ((824 / 823) * (6584 / 6582)))
    else if p = 7 then (8 / 7) * ((14 / 13) * ((104 / 103) * ((824 / 823) * (6584 / 6582))))
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp; dsimp only [β]
    by_cases h3 : p = 3
    · subst h3; norm_num
    rw [if_neg h3]; by_cases h5 : p = 5
    · subst h5; norm_num
    rw [if_neg h5]; by_cases h31 : p = 31
    · exact absurd (h31 ▸ hp) h31P
    rw [if_neg h31]; by_cases h61 : p = 61
    · exact absurd (h61 ▸ hp) h61P
    rw [if_neg h61]; by_cases h127 : p = 127
    · exact absurd (h127 ▸ hp) h127P
    rw [if_neg h127]; by_cases h991 : p = 991
    · subst h991; norm_num
    rw [if_neg h991]; by_cases h823 : p = 823
    · subst h823; norm_num
    rw [if_neg h823]; by_cases h103 : p = 103
    · subst h103; norm_num
    rw [if_neg h103]; by_cases h13 : p = 13
    · subst h13; norm_num
    rw [if_neg h13]; by_cases h7 : p = 7
    · subst h7; norm_num
    rw [if_neg h7]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  refine graham_contra (e0 := 3) (zB := ((1 * ((992 / 991) * (7928 / 7926))) * (1984 / 1982)) *
      (((7688 / 7686) * (15376 / 15374)) * ((31 : ℚ) ^ 3 / ((31 : ℚ) ^ 3 - 3))))
    hP (by norm_num) hm he3 E β hB ?_ ?_
    (fun L hLp hLz hLβ => by
      have h := zleaf_k6_j2_bound (z := 31) (by norm_num) (by norm_num) {61, 991} {7687}
        hS_z31 hS_z31_j2 hLp hLz hLβ
        (fun q hq => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl <;> (dsimp only [β]; norm_num))
        (fun q hq => by rw [Finset.mem_singleton.mp hq]; dsimp only [β]; norm_num)
      refine h.trans (le_of_eq ?_)
      rw [Finset.prod_pair (by norm_num), Finset.prod_singleton]
      dsimp only [β]; norm_num) ?_
  · intro p hp c hcP hcd hmin hne
    have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := (hB p hp).2
    dsimp only [β] at hne
    by_cases hc3 : c = 3
    · subst hc3
      have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    rw [if_neg hc3] at hne; by_cases hc5 : c = 5
    · subst hc5
      exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
    rw [if_neg hc5] at hne; by_cases hc31 : c = 31
    · exact absurd (hc31 ▸ hcP) h31P
    rw [if_neg hc31] at hne; by_cases hc61 : c = 61
    · exact absurd (hc61 ▸ hcP) h61P
    rw [if_neg hc61] at hne; by_cases hc127 : c = 127
    · exact absurd (hc127 ▸ hcP) h127P
    rw [if_neg hc127] at hne; by_cases hc991 : c = 991
    · subst hc991
      have hp7927 : 7927 ≤ p := parent_ge_7927_of_c991 (hP p hp).1 (hP p hp).2 hcd
      have hle : β p ≤ 7928 / 7926 := hBp.trans ((B_anti (by norm_num : 2 ≤ 7927) hp7927).trans (by norm_num))
      have hβc : β 991 = (992 / 991) * (7928 / 7926) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (991 : ℚ)) * β p ≤ (1 + 1 / (991 : ℚ)) * (7928 / 7926) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    rw [if_neg hc991] at hne; by_cases hc823 : c = 823
    · subst hc823
      have hp6583 : 6583 ≤ p := parent_ge_6583_of_c823_z31 (hP p hp).1 (hP p hp).2 hcd hmin
      have hle : β p ≤ 6584 / 6582 := hBp.trans ((B_anti (by norm_num : 2 ≤ 6583) hp6583).trans (by norm_num))
      have hβc : β 823 = (824 / 823) * (6584 / 6582) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (823 : ℚ)) * β p ≤ (1 + 1 / (823 : ℚ)) * (6584 / 6582) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    rw [if_neg hc823] at hne; by_cases hc103 : c = 103
    · subst hc103
      by_cases hp823 : p = 823
      · rw [hp823]; dsimp only [β]; norm_num
      · have hp1441 : 1441 ≤ p := parent_ge_1441_of_c103_z31 (hP p hp).1 (hP p hp).2 hp823 hcd hmin
        have hle : β p ≤ 1442 / 1440 := hBp.trans ((B_anti (by norm_num : 2 ≤ 1441) hp1441).trans (by norm_num))
        have hβc : β 103 = (104 / 103) * ((824 / 823) * (6584 / 6582)) := by dsimp only [β]; norm_num
        rw [hβc]
        have : (1 + 1 / (103 : ℚ)) * β p ≤ (1 + 1 / (103 : ℚ)) * (1442 / 1440) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith
    rw [if_neg hc103] at hne; by_cases hc13 : c = 13
    · subst hc13
      have hpeq : p = 103 := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 103 h103P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    rw [if_neg hc13] at hne; by_cases hc7 : c = 7
    · subst hc7
      have hpeq : p = 13 := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 13 h13P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    rw [if_neg hc7] at hne
    exact absurd rfl hne
  · dsimp only [β]; norm_num
  · dsimp only [β]; norm_num

private theorem kill_mod2_z31_13in_103out {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h31P : 31 ∉ P) (h13P : 13 ∈ P) (h103P : 103 ∉ P) (hm : 20 ≤ m) (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 31 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 31 ^ e * ∏ p ∈ P, p) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 31) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 31 → c ∉ ({31} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, S6, -, -⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 5 h5P (by norm_num)
  have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 h13P (by norm_num)
  have h61P : 61 ∉ P := fun h61 =>
    weight_kill hP E (L := [3, 5, 7, 13, 61]) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by norm_num)
  have h883P : 883 ∉ P := fun h883 => by
    have h17P : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 883 h883 (by norm_num)
    exact S6 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 17 h17P (by norm_num)
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 31 then 1
    else if p = 61 then 1
    else if p = 991 then (992 / 991) * (7928 / 7926)
    else if p = 127 then (128 / 127) * (2032 / 2030)
    else if p = 13 then (14 / 13) * (1001 / 999)
    else if p = 7 then (8 / 7) * ((14 / 13) * (1001 / 999))
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp; dsimp only [β]
    by_cases h3 : p = 3
    · subst h3; norm_num
    rw [if_neg h3]; by_cases h5 : p = 5
    · subst h5; norm_num
    rw [if_neg h5]; by_cases h31 : p = 31
    · exact absurd (h31 ▸ hp) h31P
    rw [if_neg h31]; by_cases h61 : p = 61
    · exact absurd (h61 ▸ hp) h61P
    rw [if_neg h61]; by_cases h991 : p = 991
    · subst h991; norm_num
    rw [if_neg h991]; by_cases h127 : p = 127
    · subst h127; norm_num
    rw [if_neg h127]; by_cases h13 : p = 13
    · subst h13; norm_num
    rw [if_neg h13]; by_cases h7 : p = 7
    · subst h7; norm_num
    rw [if_neg h7]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  refine graham_contra (e0 := 3) (zB := ((1 * ((992 / 991) * (7928 / 7926))) * (1984 / 1982)) *
      (((7688 / 7686) * (15376 / 15374)) * ((31 : ℚ) ^ 3 / ((31 : ℚ) ^ 3 - 3))))
    hP (by norm_num) hm he3 E β hB ?_ ?_
    (fun L hLp hLz hLβ => by
      have h := zleaf_k6_j2_bound (z := 31) (by norm_num) (by norm_num) {61, 991} {7687}
        hS_z31 hS_z31_j2 hLp hLz hLβ
        (fun q hq => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl <;> (dsimp only [β]; norm_num))
        (fun q hq => by rw [Finset.mem_singleton.mp hq]; dsimp only [β]; norm_num)
      refine h.trans (le_of_eq ?_)
      rw [Finset.prod_pair (by norm_num), Finset.prod_singleton]
      dsimp only [β]; norm_num) ?_
  · intro p hp c hcP hcd hmin hne
    have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := (hB p hp).2
    dsimp only [β] at hne
    by_cases hc3 : c = 3
    · subst hc3
      have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    rw [if_neg hc3] at hne; by_cases hc5 : c = 5
    · subst hc5
      exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
    rw [if_neg hc5] at hne; by_cases hc31 : c = 31
    · exact absurd (hc31 ▸ hcP) h31P
    rw [if_neg hc31] at hne; by_cases hc61 : c = 61
    · exact absurd (hc61 ▸ hcP) h61P
    rw [if_neg hc61] at hne; by_cases hc991 : c = 991
    · subst hc991
      have hp7927 : 7927 ≤ p := parent_ge_7927_of_c991 (hP p hp).1 (hP p hp).2 hcd
      have hle : β p ≤ 7928 / 7926 := hBp.trans ((B_anti (by norm_num : 2 ≤ 7927) hp7927).trans (by norm_num))
      have hβc : β 991 = (992 / 991) * (7928 / 7926) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (991 : ℚ)) * β p ≤ (1 + 1 / (991 : ℚ)) * (7928 / 7926) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    rw [if_neg hc991] at hne; by_cases hc127 : c = 127
    · subst hc127
      have hp2031 : 2031 ≤ p := parent_ge_2031_of_c127_z31 (hP p hp).1 (hP p hp).2 hcd hmin
      have hle : β p ≤ 2032 / 2030 := hBp.trans ((B_anti (by norm_num : 2 ≤ 2031) hp2031).trans (by norm_num))
      have hβc : β 127 = (128 / 127) * (2032 / 2030) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (127 : ℚ)) * β p ≤ (1 + 1 / (127 : ℚ)) * (2032 / 2030) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    rw [if_neg hc127] at hne; by_cases hc13 : c = 13
    · subst hc13
      have hp103 : p ≠ 103 := fun h => h103P (h ▸ hp)
      have hp883 : p ≠ 883 := fun h => h883P (h ▸ hp)
      have hsq13 : ¬ 13 * 13 ∣ p + 1 := S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
      have hp1000 : 1000 ≤ p := parent_ge_1000_of_c13 (hP p hp).1 (hP p hp).2 hp103 hp883
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcd hmin hsq13
      have hle : β p ≤ 1001 / 999 := hBp.trans ((B_anti (by norm_num : 2 ≤ 1000) hp1000).trans (by norm_num))
      have hβc : β 13 = (14 / 13) * (1001 / 999) := by dsimp only [β]; norm_num
      rw [hβc]
      have : (1 + 1 / (13 : ℚ)) * β p ≤ (1 + 1 / (13 : ℚ)) * (1001 / 999) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      linarith
    rw [if_neg hc13] at hne; by_cases hc7 : c = 7
    · subst hc7
      have hpeq : p = 13 := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 13 h13P hcd (by norm_num)
      rw [hpeq]; dsimp only [β]; norm_num
    rw [if_neg hc7] at hne
    exact absurd rfl hne
  · dsimp only [β]; norm_num
  · dsimp only [β]; norm_num

private theorem kill_mod2_z31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h31P : 31 ∉ P) (hm : 20 ≤ m) (he3 : 3 ≤ e) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 31 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 31 ^ e * ∏ p ∈ P, p) :
    False := by
  by_cases h13P : 13 ∈ P
  · by_cases h103P : 103 ∈ P
    · exact kill_mod2_z31_13in_103in hP h31P h13P h103P hm he3 hm2 E
    · exact kill_mod2_z31_13in_103out hP h31P h13P h103P hm he3 hm2 E
  · have hK := prime_dvd_prime_pow (e := e) (z := 31) (by norm_num)
    have hnz : ∀ {c : ℕ}, c ≠ 31 → c ∉ ({31} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
    obtain ⟨S1, S2, S3, S4, -, S6, -, -⟩ := facts hP hK E
    have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
    have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
    have h181P : 181 ∉ P := fun h181 =>
      h13P (S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 h181 (by norm_num))
    let β : ℕ → ℚ := fun p =>
      if p = 3 then 8 / 5
      else if p = 5 then 6 / 5
      else if p = 31 then 1
      else if p = 7 then (8 / 7) * (224 / 222)
      else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    refine graham_contra (e0 := 3) hP (by norm_num) hm he3 E β ?_ ?_ ?_
      (fun L hLp hLz hLβ => by
        have h := zleaf_k6_bound (z := 31) (by norm_num) (by norm_num) {61, 991} hS_z31 hLp hLz hLβ
          (fun q hq => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl <;> (dsimp only [β]; norm_num))
        simpa [β] using h) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3 h5 h31 h7
      · subst h3; norm_num
      · subst h5; norm_num
      · exact absurd (h31 ▸ hp) h31P
      · subst h7; norm_num
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c hcP hcd hmin hne
      have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
        dsimp only [β]
        split_ifs with h3 h5 h31 h7
        · subst h3; norm_num
        · subst h5; norm_num
        · exact absurd (h31 ▸ hp) h31P
        · subst h7; norm_num
        · exact le_rfl
      dsimp only [β] at hne
      split_ifs at hne with hc3 hc5 hc31 hc7
      · subst hc3
        have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
        rw [hpeq]; dsimp only [β]; norm_num
      · subst hc5
        exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
      · exact absurd (hc31 ▸ hcP) h31P
      · subst hc7
        have hp13 : p ≠ 13 := fun h => h13P (h ▸ hp)
        have hp181 : p ≠ 181 := fun h => h181P (h ▸ hp)
        have hsq7 : ¬ 7 * 7 ∣ p + 1 := S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
        have hp223 : 223 ≤ p := parent_ge_223_of_c7 (hP p hp).1 (hP p hp).2 hp13 hp181
          (by norm_num) (by norm_num) hcd hmin hsq7
        have hle : β p ≤ 224 / 222 := hBp.trans ((B_anti (by norm_num : 2 ≤ 223) hp223).trans (by norm_num))
        have hβc : β 7 = (8 / 7) * (224 / 222) := by dsimp only [β]; norm_num
        rw [hβc]
        have : (1 + 1 / (7 : ℚ)) * β p ≤ (1 + 1 / (7 : ℚ)) * (224 / 222) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith
      · exact absurd rfl hne
    · dsimp only [β]; norm_num
    · dsimp only [β]; norm_num

private theorem kill_mod2_z7 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h7P : 7 ∉ P) (hm : 20 ≤ m) (he41 : 41 ≤ e) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) (z := 7) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, S4, -, -, -, -⟩ := facts hP hK E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  by_cases h13P : 13 ∈ P
  · let β : ℕ → ℚ := fun p =>
      if p = 3 then 8 / 5
      else if p = 5 then 6 / 5
      else if p = 7 then 1
      else if p = 13 then (14 / 13) * (104 / 102)
      else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    refine graham_contra (e0 := 41) hP (by norm_num) hm he41 E β ?_ ?_ ?_
      (fun L hLp hLz hLβ => by
        have h := zleaf_k6_j2_bound (z := 7) (by norm_num) (by norm_num) {13, 223} {97}
          hS_z7 hS_z7_j2 hLp hLz hLβ
          (fun q hq => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl <;> (dsimp only [β]; norm_num))
          (fun q hq => by rw [Finset.mem_singleton.mp hq]; dsimp only [β]; norm_num)
        simpa [β] using h) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3 h5 h7 h13
      · subst h3; norm_num
      · subst h5; norm_num
      · exact absurd (h7 ▸ hp) h7P
      · subst h13; norm_num
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c hcP hcd _ hne
      have hBp : β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
        dsimp only [β]
        split_ifs with h3 h5 h7 h13
        · subst h3; norm_num
        · subst h5; norm_num
        · exact absurd (h7 ▸ hp) h7P
        · subst h13; norm_num
        · exact le_rfl
      dsimp only [β] at hne
      split_ifs at hne with hc3 hc5 hc7 hc13
      · subst hc3
        have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
        rw [hpeq]; dsimp only [β]; norm_num
      · subst hc5
        exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
      · exact absurd (hc7 ▸ hcP) h7P
      · subst hc13
        have hp103 : 103 ≤ p := parent_ge_103_of_c13 (hP p hp).1 (hP p hp).2 hcd
        have hle : β p ≤ 104 / 102 := hBp.trans ((B_anti (by norm_num : 2 ≤ 103) hp103).trans (by norm_num))
        have hβc : β 13 = (14 / 13) * (104 / 102) := by dsimp only [β]; norm_num
        rw [hβc]
        have : (1 + 1 / (13 : ℚ)) * β p ≤ (1 + 1 / (13 : ℚ)) * (104 / 102) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith
      · exact absurd rfl hne
    · dsimp only [β]; norm_num
    · dsimp only [β]; norm_num
  · let β : ℕ → ℚ := fun p =>
      if p = 3 then 8 / 5
      else if p = 5 then 6 / 5
      else if p = 7 then 1
      else if p = 13 then 1
      else ((p : ℚ) + 1) / ((p : ℚ) - 1)
    refine graham_contra (e0 := 41) hP (by norm_num) hm he41 E β ?_ ?_ ?_
      (fun L hLp hLz hLβ => by
        have h := zleaf_k6_bound (z := 7) (by norm_num) (by norm_num) {13, 223} hS_z7 hLp hLz hLβ
          (fun q hq => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl <;> (dsimp only [β]; norm_num))
        simpa [β] using h) ?_
    · intro p hp
      dsimp only [β]
      split_ifs with h3 h5 h7 h13
      · subst h3; norm_num
      · subst h5; norm_num
      · exact absurd (h7 ▸ hp) h7P
      · exact absurd (h13 ▸ hp) h13P
      · exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
    · intro p hp c hcP hcd _ hne
      dsimp only [β] at hne
      split_ifs at hne with hc3 hc5 hc7 hc13
      · subst hc3
        have hpeq : p = 5 := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
        rw [hpeq]; dsimp only [β]; norm_num
      · subst hc5
        exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
      · exact absurd (hc7 ▸ hcP) h7P
      · exact absurd (hc13 ▸ hcP) h13P
      · exact absurd rfl hne
    · dsimp only [β]; norm_num
    · dsimp only [β]; norm_num

-- Section 5. Main theorem dispatching all 69 primes.

end OMA.P_Erdos1052_H4_R1_H1

open OMA.P_Erdos1052_H4_R1_H1 in
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main in
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main in
theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1.H1 := by
  refine ⟨20, fun n hn z hz hS he_odd hzmem _ h2even hz7_hyp _ _ _ _ _ _ _ _ _ _ => ?_⟩
  by_cases ha : padicValNat 2 n ≤ 20
  · exact ha
  exfalso
  have ha20 : 20 ≤ padicValNat 2 n := by omega
  have hn0 : n ≠ 0 := hn.2.ne'
  have h2_eq : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hz_dvd, hsimple⟩ := simple_of_unique_repeated hn0 hS
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hz_dvd, hn0⟩
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzsq : z ^ 2 ∣ n := ((hS z).mpr rfl).2.2
  have he2 : 2 ≤ n.factorization z := (hz.pow_dvd_iff_le_factorization hn0).mp hzsq
  have he3 : 3 ≤ n.factorization z := by
    have := Nat.odd_iff.mp he_odd
    omega
  obtain ⟨hP, E⟩ := kernel_balance_one hn hzpf hz2 hsimple
  set P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ))
  have hzP : z ∉ P := fun h => (Finset.mem_filter.mp h).2 (Finset.mem_singleton_self z)
  have hm20 : 20 ≤ n.factorization 2 := h2_eq ▸ ha20
  have hm0 : n.factorization 2 ≠ 0 := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
  rcases hzmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- z = 7
    have he41 : 41 ≤ n.factorization 7 := (hz7_hyp rfl).1
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_z7 hP hzP hm20 he41 hm2 E
    · exact kill_not_mod2_generic (e0 := 41) {13, 223} hP hz (by norm_num) (by norm_num) hzP
        hm20 he41 hm2 hS_z7 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 11
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 13
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_z13 hP hm20 he_odd he3 hm2 E
    · exact kill_not_mod2_generic (e0 := 3) {103} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z13 (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun _ => Dvd.dvd.trans (by norm_num : 7 ∣ 13 + 1) (dvd_one_add_pow_of_odd he_odd)) E (by norm_num)
  · -- z = 19
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 23
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 31
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_z31 hP hzP hm20 he3 hm2 E
    · exact kill_not_mod2_generic (e0 := 3) {61, 991} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z31 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 37
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 19) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 41
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      ⟨5, ⟨2, rfl⟩, by decide⟩ E
  · -- z = 43
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 47
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 61
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_31chain {487, 1951} hP hz (by norm_num) hm20 he_odd he3 hm2
        (Or.inl (by norm_num)) hS_z61 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) {487, 1951} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z61 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 73
    exact kill_c3 hP hz (by norm_num) hm0 he_odd E (p1 := 37) (p2 := 19) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 79
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 83
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 103
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_13dvd {823} hP hz (by norm_num) hm20 he_odd he3 hm2
        (by norm_num) hS_z103 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) {823} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z103 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 127
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_z127 hP hzP hm20 he3 hm2 E
    · exact kill_not_mod2_generic (e0 := 3) ∅ hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z127 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 139
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 151
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 19) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 157
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 79) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 163
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 167
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 191
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 223
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_7dvd {1783} hP hz (by norm_num) hm20 he_odd he3 hm2
        (by norm_num) hS_z223 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) {1783} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z223 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 277
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 139) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 307
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 311
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 313
    exact kill_c3 hP hz (by norm_num) hm0 he_odd E (p1 := 157) (p2 := 79) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 331
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 83) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 367
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 383
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 433
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_7dvd {3463} hP hz (by norm_num) hm20 he_odd he3 hm2
        (by norm_num) hS_z433 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) {3463} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z433 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 487
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_31chain {15583} hP hz (by norm_num) hm20 he_odd he3 hm2
        (Or.inr ⟨by norm_num, by norm_num⟩) hS_z487 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) {15583} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z487 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 571
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 601
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 43) (q := 11)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 607
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 19) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 613
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 307) (q := 11)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 617
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      ⟨77, ⟨38, rfl⟩, by rw [show (77 : ℕ) = 11 * 7 from rfl, pow_mul, show (16 : ZMod 617) ^ 11 = 142 from by decide]; decide⟩ E
  · -- z = 619
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 631
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 79) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 643
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 661
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 331) (q := 83)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 733
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 367) (q := 23)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 743
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 751
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 761
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      ⟨95, ⟨47, rfl⟩, by rw [show (95 : ℕ) = 19 * 5 from rfl, pow_mul, show (16 : ZMod 761) ^ 19 = 168 from by decide]; decide⟩ E
  · -- z = 823
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_z823 hP hm20 he_odd he3 hm2 E
    · exact kill_not_mod2_generic (e0 := 3) ∅ hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z823 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 853
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_7dvd {6823} hP hz (by norm_num) hm20 he_odd he3 hm2
        (by norm_num) hS_z853 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) {6823} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z853 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 991
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_31chain {7927} hP hz (by norm_num) hm20 he_odd he3 hm2
        (Or.inl (by norm_num)) hS_z991 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) {7927} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z991 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 1039
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1063
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 19) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1117
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 43) (q := 11)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1201
    exact kill_c3 hP hz (by norm_num) hm0 he_odd E (p1 := 601) (p2 := 43) (q := 11)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1213
    exact kill_c3 hP hz (by norm_num) hm0 he_odd E (p1 := 607) (p2 := 19) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1231
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1237
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 619) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1279
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1301
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      ⟨325, ⟨162, rfl⟩, by rw [show (325 : ℕ) = 25 * 13 from rfl, pow_mul, show (16 : ZMod 1301) ^ 25 = 78 from by decide]; decide⟩ E
  · -- z = 1303
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 163) (q := 41)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1321
    exact kill_c3 hP hz (by norm_num) hm0 he_odd E (p1 := 661) (p2 := 331) (q := 83)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1327
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 83) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1471
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1487
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 1523
    exact kill_z_mod3_2 hP hz (by norm_num) (by norm_num) hm0 (h2_eq ▸ h2even (by norm_num)) he_odd
      (pow16_odd_of_mod4_eq3 hz (by norm_num)) E
  · -- z = 1531
    exact kill_c1 hP hz (by norm_num) hm0 he_odd E (q := 383) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- z = 1663
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_13dvd ∅ hP hz (by norm_num) hm20 he_odd he3 hm2
        (by norm_num) hS_z1663 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) ∅ hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z1663 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 1777
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_7dvd ∅ hP hz (by norm_num) hm20 he_odd he3 hm2
        (by norm_num) hS_z1777 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) ∅ hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z1777 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 1783
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_z1783 hP hm20 he_odd he3 hm2 E
    · exact kill_not_mod2_generic (e0 := 3) ∅ hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z1783 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 1951
    by_cases hm2 : n.factorization 2 % 4 = 2
    · exact kill_mod2_31chain {15607} hP hz (by norm_num) hm20 he_odd he3 hm2
        (Or.inr ⟨by norm_num, by norm_num⟩) hS_z1951 (by decide) (by decide) E (by norm_num)
    · exact kill_not_mod2_generic (e0 := 3) {15607} hP hz (by norm_num) (by norm_num) hzP
        hm20 he3 hm2 hS_z1951 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) E (by norm_num)
  · -- z = 2053
    exact kill_c2 hP hz (by norm_num) hm0 he_odd E (p1 := 79) (q := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
