import OMAStatements.S_oeis_a227071
import Mathlib

namespace OMA.A227071Proof

open OMA.S_oeis_a227071

/-! ## Digits and the membership test -/

theorem len_eq (k E : ℕ) (h1 : 10 ^ E ≤ k) (h2 : k < 10 ^ (E + 1)) :
    (Nat.digits 10 k).length = E + 1 :=
  le_antisymm ((Nat.digits_length_le_iff (by norm_num) k).2 h2)
    (Nat.succ_le_of_lt ((Nat.lt_digits_length_iff (by norm_num) k).2 h1))

theorem mem_s_iff (m k : ℕ) (hk : 0 < k) :
    k ∈ s m ↔ k ^ m ≡ k [MOD 10 ^ (Nat.digits 10 k).length] := by
  have hlt : k < 10 ^ (Nat.digits 10 k).length := Nat.lt_base_pow_length_digits (by norm_num)
  show (0 < k ∧ k ^ m % 10 ^ (Nat.digits 10 k).length = k) ↔
    k ^ m % 10 ^ (Nat.digits 10 k).length = k % 10 ^ (Nat.digits 10 k).length
  rw [Nat.mod_eq_of_lt hlt]
  exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩

theorem ten_pow (D : ℕ) : (10 : ℕ) ^ D = 2 ^ D * 5 ^ D := by
  have h : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h, mul_pow]

/-! ## Congruence tools -/

theorem pow_gcd_modEq {x a b q : ℕ} (ha : x ^ a ≡ 1 [MOD q]) (hb : x ^ b ≡ 1 [MOD q]) :
    x ^ (Nat.gcd a b) ≡ 1 [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff] at ha hb ⊢
  push_cast at ha hb ⊢
  exact pow_gcd_eq_one.2 ⟨ha, hb⟩

theorem modEq_succ_iff (q k m : ℕ) (hc : Nat.Coprime q k) :
    k ^ (m + 1) ≡ k [MOD q] ↔ k ^ m ≡ 1 [MOD q] := by
  rw [pow_succ]
  constructor
  · intro h
    have h' : k ^ m * k ≡ 1 * k [MOD q] := by rwa [one_mul]
    exact Nat.ModEq.cancel_right_of_coprime hc h'
  · intro h
    have h' := h.mul_right k
    rwa [one_mul] at h'

/-- If `p ∣ k`, then `k ^ (m + 1) ≡ k` modulo `p ^ D` holds exactly when `p ^ D ∣ k`. -/
theorem modEq_of_dvd_iff (p D k m : ℕ) (hp : p.Prime) (hpk : p ∣ k) (hk : 0 < k) (hm : 0 < m) :
    k ^ (m + 1) ≡ k [MOD p ^ D] ↔ p ^ D ∣ k := by
  constructor
  · intro h
    have hle : k ≤ k ^ (m + 1) := Nat.le_self_pow (by omega) k
    have h1 : p ^ D ∣ k ^ (m + 1) - k := (Nat.modEq_iff_dvd' hle).1 h.symm
    have h2 : k ^ (m + 1) - k = k * (k ^ m - 1) := by
      rw [pow_succ', Nat.mul_sub_one]
    rw [h2] at h1
    have hkm : 1 ≤ k ^ m := Nat.one_le_pow _ _ hk
    have hnd : ¬ p ∣ k ^ m - 1 := by
      intro hd
      have h3 : p ∣ k ^ m := dvd_pow hpk (by omega)
      have h4 : p ∣ k ^ m - (k ^ m - 1) := Nat.dvd_sub h3 hd
      rw [show k ^ m - (k ^ m - 1) = 1 by omega] at h4
      exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
    have hc : Nat.Coprime (p ^ D) (k ^ m - 1) :=
      Nat.Coprime.pow_left D ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    exact hc.dvd_of_dvd_mul_right h1
  · intro h
    have h0 : k ≡ 0 [MOD p ^ D] := Nat.modEq_zero_iff_dvd.2 h
    have h0' : k ^ (m + 1) ≡ 0 [MOD p ^ D] :=
      Nat.modEq_zero_iff_dvd.2 (h.trans (dvd_pow_self k (by omega)))
    exact h0'.trans h0.symm

theorem cop_tot (p r D : ℕ) (hp : p.Prime) (hrp : Nat.Coprime r p) (hr1 : Nat.Coprime r (p - 1)) :
    Nat.Coprime r (Nat.totient (p ^ D)) := by
  cases D with
  | zero => simp
  | succ D =>
    rw [Nat.totient_prime_pow_succ hp]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right D hrp) hr1

/-- Modulo a prime power `p ^ D`: with `n = g * r` and `r` coprime to `φ (p ^ D)`, the exponents `n + 1` and
`g + 1` select the same `k`. -/
theorem modp_iff (p D k n g r : ℕ) (hp : p.Prime) (hk : 0 < k) (hn : n = g * r) (hn0 : 0 < n)
    (hg : 0 < g) (hr : Nat.Coprime r (Nat.totient (p ^ D))) :
    k ^ (n + 1) ≡ k [MOD p ^ D] ↔ k ^ (g + 1) ≡ k [MOD p ^ D] := by
  by_cases hpk : p ∣ k
  · exact (modEq_of_dvd_iff p D k n hp hpk hk hn0).trans
      (modEq_of_dvd_iff p D k g hp hpk hk hg).symm
  · have hc : Nat.Coprime (p ^ D) k :=
      Nat.Coprime.pow_left D ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
    rw [modEq_succ_iff _ _ _ hc, modEq_succ_iff _ _ _ hc]
    constructor
    · intro h
      have h1 : k ^ (g * r) ≡ 1 [MOD p ^ D] := by rw [← hn]; exact h
      have h2 : k ^ (g * Nat.totient (p ^ D)) ≡ 1 [MOD p ^ D] := by
        rw [mul_comm, pow_mul]
        simpa using (Nat.ModEq.pow_totient hc.symm).pow g
      have h3 := pow_gcd_modEq h1 h2
      rwa [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hr, mul_one] at h3
    · intro h
      rw [hn, pow_mul]
      simpa using h.pow r

/-- Part (i): `k ^ (n + 1) ≡ k` and `k ^ (g + 1) ≡ k` modulo `10 ^ D` agree when `n = g * r`, `r` coprime to `10`. -/
theorem key10 (n g r k D : ℕ) (hk : 0 < k) (hn : n = g * r) (hn0 : 0 < n) (hg : 0 < g)
    (hr2 : ¬ 2 ∣ r) (hr5 : ¬ 5 ∣ r) :
    k ^ (n + 1) ≡ k [MOD 10 ^ D] ↔ k ^ (g + 1) ≡ k [MOD 10 ^ D] := by
  have hp5 : Nat.Prime 5 := by norm_num
  have c2 : Nat.Coprime r 2 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hr2)
  have c5 : Nat.Coprime r 5 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp5).2 hr5)
  have t2 : Nat.Coprime r (Nat.totient (2 ^ D)) := cop_tot 2 r D Nat.prime_two c2 (by norm_num)
  have t5 : Nat.Coprime r (Nat.totient (5 ^ D)) := cop_tot 5 r D hp5 c5 (by
    have h4 : (5 : ℕ) - 1 = 2 ^ 2 := by norm_num
    rw [h4]
    exact Nat.Coprime.pow_right 2 c2)
  have c25 : Nat.Coprime (2 ^ D) (5 ^ D) := Nat.Coprime.pow D D (by norm_num)
  rw [ten_pow, ← Nat.modEq_and_modEq_iff_modEq_mul c25, ← Nat.modEq_and_modEq_iff_modEq_mul c25]
  exact and_congr (modp_iff 2 D k n g r Nat.prime_two hk hn hn0 hg t2)
    (modp_iff 5 D k n g r hp5 hk hn hn0 hg t5)

theorem s_eq (n g r : ℕ) (hn : n = g * r) (hn0 : 0 < n) (hg : 0 < g) (hr2 : ¬ 2 ∣ r)
    (hr5 : ¬ 5 ∣ r) : s (g + 1) = s (n + 1) := by
  ext k
  by_cases hk : 0 < k
  · rw [mem_s_iff _ k hk, mem_s_iff _ k hk]
    exact (key10 n g r k _ hk hn hn0 hg hr2 hr5).symm
  · exact ⟨fun h => absurd h.1 hk, fun h => absurd h.1 hk⟩

/-! ## Exact orders (lifting the exponent by hand) -/

theorem modEq_one_of (q c v : ℕ) (h : q ∣ c) : 1 + c * v ≡ 1 [MOD q] := by
  obtain ⟨d, rfl⟩ := h
  show (1 + q * d * v) % q = 1 % q
  rw [mul_assoc]
  exact Nat.add_mul_mod_self_left 1 q (d * v)

theorem not_modEq_one (p e f v : ℕ) (hf : f = e + 1) (hp : 0 < p) (hv : ¬ p ∣ v) :
    ¬ 1 + p ^ e * v ≡ 1 [MOD p ^ f] := by
  subst hf
  intro h
  have h1 : p ^ (e + 1) ∣ 1 + p ^ e * v - 1 := (Nat.modEq_iff_dvd' (by omega)).1 h.symm
  rw [Nat.add_sub_cancel_left, pow_succ] at h1
  exact hv ((mul_dvd_mul_iff_left (pow_ne_zero e hp.ne')).1 h1)

theorem ord_iff (p B x q M : ℕ) (hp : p.Prime) (h1 : x ^ (p ^ (B + 1)) ≡ 1 [MOD q])
    (h2 : ¬ x ^ (p ^ B) ≡ 1 [MOD q]) : x ^ M ≡ 1 [MOD q] ↔ p ^ (B + 1) ∣ M := by
  constructor
  · intro hM
    have hg := pow_gcd_modEq hM h1
    obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right M (p ^ (B + 1)))
    rw [hgi] at hg
    by_cases hiB : i ≤ B
    · exfalso
      apply h2
      obtain ⟨c, hc⟩ : p ^ i ∣ p ^ B := pow_dvd_pow p hiB
      rw [hc, pow_mul]
      simpa using hg.pow c
    · have hi' : i = B + 1 := by omega
      have hd := Nat.gcd_dvd_left M (p ^ (B + 1))
      rwa [hgi, hi'] at hd
  · rintro ⟨c, rfl⟩
    rw [pow_mul]
    simpa using h1.pow c

theorem pow2_lemma (u : ℕ) (hu : Odd u) (j : ℕ) :
    ∃ v, Odd v ∧ (1 + 4 * u) ^ 2 ^ j = 1 + 2 ^ (j + 2) * v := by
  induction j with
  | zero => exact ⟨u, hu, by norm_num⟩
  | succ j ih =>
    obtain ⟨v, hv, h⟩ := ih
    refine ⟨v + 2 ^ (j + 1) * v ^ 2,
      hv.add_even ((Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _), ?_⟩
    have e : (1 + 4 * u) ^ 2 ^ (j + 1) = ((1 + 4 * u) ^ 2 ^ j) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    rw [e, h]
    ring

theorem pow5_lemma (u : ℕ) (hu : ¬ 5 ∣ u) (j : ℕ) :
    ∃ v, ¬ 5 ∣ v ∧ (1 + 5 * u) ^ 5 ^ j = 1 + 5 ^ (j + 1) * v := by
  induction j with
  | zero => exact ⟨u, hu, by norm_num⟩
  | succ j ih =>
    obtain ⟨v, hv, h⟩ := ih
    refine ⟨v + 5 * (2 * 5 ^ j * v ^ 2 + 10 * (5 ^ j) ^ 2 * v ^ 3 + 25 * (5 ^ j) ^ 3 * v ^ 4
      + 25 * (5 ^ j) ^ 4 * v ^ 5), fun hd => hv (by omega), ?_⟩
    have e : (1 + 5 * u) ^ 5 ^ (j + 1) = ((1 + 5 * u) ^ 5 ^ j) ^ 5 := by
      rw [← pow_mul, ← pow_succ]
    rw [e, h]
    ring

theorem witness_iff (k D q1 q2 M : ℕ) (hq : 10 ^ D = q1 * q2) (hcop : Nat.Coprime q1 q2)
    (htriv : k ≡ 1 [MOD q2]) (hunit : Nat.Coprime q1 k) :
    k ^ (M + 1) ≡ k [MOD 10 ^ D] ↔ k ^ M ≡ 1 [MOD q1] := by
  rw [hq, ← Nat.modEq_and_modEq_iff_modEq_mul hcop, modEq_succ_iff q1 k M hunit]
  have h1 : k ^ (M + 1) ≡ 1 [MOD q2] := by simpa using htriv.pow (M + 1)
  exact ⟨fun h => h.1, fun h => ⟨h, h1.trans htriv.symm⟩⟩

/-! ## The separating witnesses -/

/-- A `k` with `k ∈ s (M + 1) ↔ 2 ^ A ∣ M`: for `A ≥ 1`, `k = 1 + 4 * 5 ^ (A + 2) * (2 ^ A - 1)`. -/
theorem sep2 (A : ℕ) : ∃ k, 0 < k ∧ ∀ M, (k ∈ s (M + 1) ↔ 2 ^ A ∣ M) := by
  cases A with
  | zero =>
    refine ⟨1, Nat.one_pos, fun M => ?_⟩
    rw [mem_s_iff (M + 1) 1 Nat.one_pos, Nat.one_pow, Nat.pow_zero]
    exact ⟨fun _ => one_dvd M, fun _ => Nat.ModEq.refl 1⟩
  | succ a =>
    obtain ⟨w, hw⟩ : ∃ w, w + 1 = 2 ^ (a + 1) :=
      ⟨2 ^ (a + 1) - 1, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))⟩
    have h2w : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (Nat.succ_ne_zero a)
    have hwodd : Odd w := by
      rw [Nat.odd_iff]
      omega
    have huodd : Odd (5 ^ (a + 3) * w) := (Odd.pow ⟨2, by norm_num⟩).mul hwodd
    have hP : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
    have hQ : 1 ≤ 5 ^ a := Nat.one_le_pow _ _ (by norm_num)
    have hw' : w + 1 = 2 * 2 ^ a := by rw [hw]; ring
    have e5 : 5 ^ (a + 3) = 125 * 5 ^ a := by ring
    have e10 : (10 : ℕ) ^ (a + 2) = 100 * (2 ^ a * 5 ^ a) := by rw [ten_pow]; ring
    have e10' : (10 : ℕ) ^ (a + 2 + 1) = 1000 * (2 ^ a * 5 ^ a) := by rw [ten_pow]; ring
    have hm2 : (w + 1) * 5 ^ a = 2 * 2 ^ a * 5 ^ a := by rw [hw']
    have hlo : 10 ^ (a + 2) ≤ 1 + 4 * (5 ^ (a + 3) * w) := by
      rw [e10, e5]
      have hm1 : 1 * 5 ^ a ≤ w * 5 ^ a := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have hhi : 1 + 4 * (5 ^ (a + 3) * w) < 10 ^ (a + 2 + 1) := by
      rw [e10', e5]
      nlinarith
    have hlen : (Nat.digits 10 (1 + 4 * (5 ^ (a + 3) * w))).length = a + 3 := by
      have := len_eq _ (a + 2) hlo hhi
      omega
    have hkpos : 0 < 1 + 4 * (5 ^ (a + 3) * w) := by omega
    refine ⟨1 + 4 * (5 ^ (a + 3) * w), hkpos, fun M => ?_⟩
    rw [mem_s_iff (M + 1) _ hkpos, hlen]
    have hcop : Nat.Coprime (2 ^ (a + 3)) (5 ^ (a + 3)) := Nat.Coprime.pow _ _ (by norm_num)
    have htriv : 1 + 4 * (5 ^ (a + 3) * w) ≡ 1 [MOD 5 ^ (a + 3)] := by
      have h4 : 4 * (5 ^ (a + 3) * w) = 5 ^ (a + 3) * (4 * w) := by ring
      rw [h4]
      exact modEq_one_of _ _ _ (dvd_refl _)
    have hunit : Nat.Coprime (2 ^ (a + 3)) (1 + 4 * (5 ^ (a + 3) * w)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    rw [witness_iff _ (a + 3) (2 ^ (a + 3)) (5 ^ (a + 3)) M (ten_pow _) hcop htriv hunit]
    obtain ⟨v1, -, e1⟩ := pow2_lemma _ huodd (a + 1)
    obtain ⟨v0, hv0, e0⟩ := pow2_lemma _ huodd a
    refine ord_iff 2 a _ _ M Nat.prime_two ?_ ?_
    · rw [e1]
      exact modEq_one_of _ _ _ (pow_dvd_pow 2 (by omega))
    · rw [e0]
      exact not_modEq_one 2 (a + 2) (a + 3) v0 (by omega) (by norm_num)
        (fun hd => by obtain ⟨t, ht⟩ := hv0; omega)

/-- A `k` with `k ∈ s (M + 1) ↔ 5 ^ B ∣ M`: for `B ≥ 1`, `k = 1 + 5 * 2 ^ (B + 1) * (5 ^ B - 1)`. -/
theorem sep5 (B : ℕ) : ∃ k, 0 < k ∧ ∀ M, (k ∈ s (M + 1) ↔ 5 ^ B ∣ M) := by
  cases B with
  | zero =>
    refine ⟨1, Nat.one_pos, fun M => ?_⟩
    rw [mem_s_iff (M + 1) 1 Nat.one_pos, Nat.one_pow, Nat.pow_zero]
    exact ⟨fun _ => one_dvd M, fun _ => Nat.ModEq.refl 1⟩
  | succ b =>
    have hp5 : Nat.Prime 5 := by norm_num
    obtain ⟨w, hw⟩ : ∃ w, w + 1 = 5 ^ (b + 1) :=
      ⟨5 ^ (b + 1) - 1, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))⟩
    have h5w : 5 ∣ 5 ^ (b + 1) := dvd_pow_self 5 (Nat.succ_ne_zero b)
    have hu : ¬ 5 ∣ 2 ^ (b + 2) * w := by
      intro h
      rcases (Nat.Prime.dvd_mul hp5).1 h with h' | h'
      · have h52 := Nat.Prime.dvd_of_dvd_pow hp5 h'
        omega
      · omega
    have hP : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by norm_num)
    have hQ : 1 ≤ 5 ^ b := Nat.one_le_pow _ _ (by norm_num)
    have hPQ : 0 < 2 ^ b * 5 ^ b := by positivity
    have hw' : w + 1 = 5 * 5 ^ b := by rw [hw]; ring
    have e2 : 2 ^ (b + 2) = 4 * 2 ^ b := by ring
    have e10 : (10 : ℕ) ^ (b + 1) = 10 * (2 ^ b * 5 ^ b) := by rw [ten_pow]; ring
    have e10' : (10 : ℕ) ^ (b + 1 + 1) = 100 * (2 ^ b * 5 ^ b) := by rw [ten_pow]; ring
    have hm2 : 2 ^ b * (w + 1) = 2 ^ b * (5 * 5 ^ b) := by rw [hw']
    have hlo : 10 ^ (b + 1) ≤ 1 + 5 * (2 ^ (b + 2) * w) := by
      rw [e10, e2]
      have hm1 : 2 ^ b * (4 * 5 ^ b) ≤ 2 ^ b * w := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have hhi : 1 + 5 * (2 ^ (b + 2) * w) < 10 ^ (b + 1 + 1) := by
      rw [e10', e2]
      nlinarith
    have hlen : (Nat.digits 10 (1 + 5 * (2 ^ (b + 2) * w))).length = b + 2 := by
      have := len_eq _ (b + 1) hlo hhi
      omega
    have hkpos : 0 < 1 + 5 * (2 ^ (b + 2) * w) := by omega
    refine ⟨1 + 5 * (2 ^ (b + 2) * w), hkpos, fun M => ?_⟩
    rw [mem_s_iff (M + 1) _ hkpos, hlen]
    have hcop : Nat.Coprime (5 ^ (b + 2)) (2 ^ (b + 2)) := Nat.Coprime.pow _ _ (by norm_num)
    have htriv : 1 + 5 * (2 ^ (b + 2) * w) ≡ 1 [MOD 2 ^ (b + 2)] := by
      have h4 : 5 * (2 ^ (b + 2) * w) = 2 ^ (b + 2) * (5 * w) := by ring
      rw [h4]
      exact modEq_one_of _ _ _ (dvd_refl _)
    have hunit : Nat.Coprime (5 ^ (b + 2)) (1 + 5 * (2 ^ (b + 2) * w)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp5).2 (by omega))
    rw [witness_iff _ (b + 2) (5 ^ (b + 2)) (2 ^ (b + 2)) M
      ((ten_pow _).trans (Nat.mul_comm _ _)) hcop htriv hunit]
    obtain ⟨v1, -, e1⟩ := pow5_lemma _ hu (b + 1)
    obtain ⟨v0, hv0, e0⟩ := pow5_lemma _ hu b
    refine ord_iff 5 b _ _ M hp5 ?_ ?_
    · rw [e1]
      exact modEq_one_of _ _ _ (pow_dvd_pow 5 (by omega))
    · rw [e0]
      exact not_modEq_one 5 (b + 1) (b + 2) v0 (by omega) (by norm_num) hv0

/-! ## Part (ii) and (iii): the lower bound -/

theorem lower (n m A B : ℕ) (hn : 1 ≤ n) (hA : 2 ^ A ∣ n) (hB : 5 ^ B ∣ n) (hm : 0 < m)
    (hs : s m = s (n + 1)) : 2 ^ A * 5 ^ B + 1 ≤ m := by
  by_cases h : m < 2
  · exfalso
    have hm1 : m = 1 := by omega
    subst hm1
    have hlen : (Nat.digits 10 10).length = 1 + 1 := len_eq 10 1 (by norm_num) (by norm_num)
    have h10 : (10 : ℕ) ∈ s 1 :=
      (mem_s_iff 1 10 (by norm_num)).2 (by unfold Nat.ModEq; rw [Nat.pow_one])
    rw [hs, mem_s_iff (n + 1) 10 (by norm_num), hlen] at h10
    have h100 : 10 ^ (1 + 1) ∣ 10 ^ (n + 1) := pow_dvd_pow 10 (by omega)
    have h3 : 0 ≡ 10 [MOD 10 ^ (1 + 1)] := (Nat.modEq_zero_iff_dvd.2 h100).symm.trans h10
    unfold Nat.ModEq at h3
    norm_num at h3
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k2, -, hk2i⟩ := sep2 A
    obtain ⟨k5, -, hk5i⟩ := sep5 B
    have h2 : k2 ∈ s (m' + 1) := by rw [hs]; exact (hk2i n).2 hA
    have h5 : k5 ∈ s (m' + 1) := by rw [hs]; exact (hk5i n).2 hB
    have hd : 2 ^ A * 5 ^ B ∣ m' :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow A B (by norm_num))
        ((hk2i m').1 h2) ((hk5i m').1 h5)
    have := Nat.le_of_dvd (by omega) hd
    omega

/-! ## A132741 -/

theorem A132741_eq (n : ℕ) (hn : n ≠ 0) :
    OMA.S_oeis_a227071.A132741 n = 2 ^ padicValNat 2 n * 5 ^ padicValNat 5 n := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  show sSup {d : ℕ | d ∣ n ∧ ∃ i j : ℕ, d = 2 ^ i * 5 ^ j} = _
  apply IsGreatest.csSup_eq
  refine ⟨⟨?_, padicValNat 2 n, padicValNat 5 n, rfl⟩, ?_⟩
  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num))
      pow_padicValNat_dvd pow_padicValNat_dvd
  · rintro d ⟨hd, i, j, rfl⟩
    have hi : i ≤ padicValNat 2 n :=
      (padicValNat_dvd_iff_le hn).1 (dvd_trans (dvd_mul_right _ _) hd)
    have hj : j ≤ padicValNat 5 n :=
      (padicValNat_dvd_iff_le hn).1 (dvd_trans (dvd_mul_left _ _) hd)
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hi)
      (Nat.pow_le_pow_right (by norm_num) hj)

theorem decomp (n : ℕ) (hn : n ≠ 0) :
    ∃ r, n = 2 ^ padicValNat 2 n * 5 ^ padicValNat 5 n * r ∧ ¬ 2 ∣ r ∧ ¬ 5 ∣ r := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨r, hr⟩ : 2 ^ padicValNat 2 n * 5 ^ padicValNat 5 n ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num))
      pow_padicValNat_dvd pow_padicValNat_dvd
  refine ⟨r, hr, ?_, ?_⟩
  · rintro ⟨t, rfl⟩
    exact pow_succ_padicValNat_not_dvd (p := 2) hn
      ⟨5 ^ padicValNat 5 n * t, hr.trans (by ring)⟩
  · rintro ⟨t, rfl⟩
    exact pow_succ_padicValNat_not_dvd (p := 5) hn
      ⟨2 ^ padicValNat 2 n * t, hr.trans (by ring)⟩

/-! ## The theorem -/

theorem main_proof :
    ∀ n ≥ 1, OMA.S_oeis_a227071.a (n + 1) = OMA.S_oeis_a227071.A132741 n + 1 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨r, hr, hr2, hr5⟩ := decomp n hn0
  rw [A132741_eq n hn0]
  have hg0 : 0 < 2 ^ padicValNat 2 n * 5 ^ padicValNat 5 n := by positivity
  have hmem : 2 ^ padicValNat 2 n * 5 ^ padicValNat 5 n + 1 ∈
      {m : ℕ | 0 < m ∧ s m = s (n + 1)} :=
    ⟨by omega, s_eq n _ r hr (by omega) hg0 hr2 hr5⟩
  show sInf {m : ℕ | 0 < m ∧ s m = s (n + 1)} = _
  apply le_antisymm (Nat.sInf_le hmem)
  obtain ⟨hm, hs⟩ := Nat.sInf_mem ⟨_, hmem⟩
  exact lower n _ _ _ hn pow_padicValNat_dvd pow_padicValNat_dvd hm hs

end OMA.A227071Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a227071.main := by
  exact OMA.A227071Proof.main_proof
