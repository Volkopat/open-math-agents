import OMAStatements.S_oeis_a270096
import Mathlib

-- Problem: OEIS A270096, a(n) = the smallest m such that 2^m == 2^n (mod n).
-- Conjecture of Robert Israel: a(n) <= n/3 for all n > 8.
-- Statement: statements/oeis-a270096.lean (declaration OMA.S_oeis_a270096.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Write n = 2^s t with t odd. If s <= m <= n, D divides n - m and 2^D = 1 (mod t), then
-- 2^m = 2^n (mod n), so a(n) <= m (lemma key). It is thus sufficient to give such m and D with
-- 3 m <= n.
-- * t = 1: then s >= 4; take m = s and D = 1.
-- * s >= 2 and t >= 3: take D = phi(t) and m = s + ((n - s) mod D) <= s + t - 2.
-- * s <= 1 and t = p^(j+1): take D = phi(t) = t - p^j and m = 2^s p^j; 3 p^j <= t.
-- * s <= 1 and t is not a prime power: t = u v with u, v coprime, odd and at least 3. Take
--   D = phi(u) phi(v) / 2, so that 2^D = 1 modulo u and modulo v, and 2 D < t. Take
--   m = s + ((n - s) mod D). For s = 0, n >= 2 D + m > 3 m. For s = 1, 3 m <= 3 D < 2 t = n.

namespace OMA.A270096

open OMA.S_oeis_a270096

lemma split (x : ℕ) (hx : 1 < x) (h : ¬ IsPrimePow x) :
    ∃ u v, x = u * v ∧ Nat.Coprime u v ∧ 1 < u ∧ 1 < v := by
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
  obtain ⟨e, r, hr, hxe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : x ≠ 0) p hp.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    apply hr
    rw [hxe, pow_zero, one_mul] at hpx
    exact hpx
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hxe
    omega
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply h
    rw [hxe, mul_one]
    exact (Nat.prime_iff.mp hp).isPrimePow.pow he
  refine ⟨p ^ e, r, hxe, Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hr),
    Nat.one_lt_pow he hp.one_lt, by omega⟩

/-- The basic tool: an exponent `m` with `s ≤ m ≤ n` and `n - m` a multiple of `D`. -/
lemma key (n s t m D : ℕ) (hn : n = 2 ^ s * t) (hsm : s ≤ m) (hmn : m ≤ n) (hD : D ∣ n - m)
    (h1 : 2 ^ D ≡ 1 [MOD t]) : a n ≤ m := by
  apply Nat.sInf_le
  show 2 ^ m ≡ 2 ^ n [MOD n]
  obtain ⟨c, hc⟩ := hD
  have h2 : 2 ^ (n - m) ≡ 1 [MOD t] := by
    rw [hc, pow_mul]
    simpa using h1.pow c
  have h3 : 2 ^ (m - s) * 1 ≡ 2 ^ (m - s) * 2 ^ (n - m) [MOD t] := (h2.mul_left _).symm
  have h4 := h3.mul_left' (2 ^ s)
  have e1 : 2 ^ s * (2 ^ (m - s) * 1) = 2 ^ m := by
    rw [mul_one, ← pow_add]
    congr 1
    omega
  have e2 : 2 ^ s * (2 ^ (m - s) * 2 ^ (n - m)) = 2 ^ n := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [e1, e2, ← hn] at h4
  exact h4

lemma three_mul_le (s : ℕ) (hs : 4 ≤ s) : 3 * s ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

/-- The exponent `s + (n - s) % D`. -/
lemma key_mod (n s t D : ℕ) (hn : n = 2 ^ s * t) (hsn : s ≤ n) (hD : 0 < D)
    (h1 : 2 ^ D ≡ 1 [MOD t]) : a n ≤ s + (n - s) % D ∧ (n - s) % D < D := by
  have hlt : (n - s) % D < D := Nat.mod_lt _ hD
  have hle : (n - s) % D ≤ n - s := Nat.mod_le _ _
  refine ⟨key n s t _ D hn (by omega) (by omega) ?_ h1, hlt⟩
  have : n - (s + (n - s) % D) = (n - s) - (n - s) % D := by omega
  rw [this]
  exact Nat.dvd_sub_mod _

lemma two_pow_totient (t : ℕ) (ht : Odd t) : 2 ^ t.totient ≡ 1 [MOD t] :=
  Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr ht)

theorem bound (n : ℕ) (h8 : 8 < n) : 3 * a n ≤ n := by
  obtain ⟨s, t, ht, hn⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have ht0 : 0 < t := ht.pos
  have hs : s < 2 ^ s := Nat.lt_two_pow_self
  have hsn : s ≤ n := by
    have : 2 ^ s * 1 ≤ 2 ^ s * t := Nat.mul_le_mul_left _ ht0
    omega
  rcases Nat.lt_or_ge t 2 with ht1 | ht2
  · -- n is a power of 2
    have : t = 1 := by omega
    subst this
    rw [mul_one] at hn
    have hs4 : 4 ≤ s := by
      by_contra hc
      have : s ≤ 3 := by omega
      have : 2 ^ s ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have := key n s 1 s 1 (by rw [mul_one]; exact hn) le_rfl hsn (one_dvd _) (Nat.modEq_one)
    have := three_mul_le s hs4
    omega
  · have ht3 : 3 ≤ t := by
      rcases ht with ⟨c, hc⟩
      omega
    rcases Nat.lt_or_ge s 2 with hs1 | hs2
    · by_cases hpp : IsPrimePow t
      · obtain ⟨p, k, hp, hk, hpk⟩ := hpp
        have hp' := hp.nat_prime
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hp3 : 3 ≤ p := by
          have hpo : Odd p := by
            have hd : p ∣ t := by rw [← hpk]; exact dvd_pow_self p (by omega)
            exact Odd.of_dvd_nat ht hd
          have := hp'.two_le
          rcases hpo with ⟨c, hc⟩
          omega
        have htot : t.totient = p ^ j * (p - 1) := by
          rw [← hpk, Nat.totient_prime_pow_succ hp']
        have hw : 0 < p ^ j := Nat.pow_pos hp'.pos
        have htw : t = p ^ j * p := by rw [← hpk, pow_succ]
        have h3w : 3 * p ^ j ≤ t := by rw [htw]; nlinarith
        have hsub : t - p ^ j = t.totient := by
          rw [htot, htw, Nat.mul_sub, mul_one]
        have h2s : 0 < 2 ^ s := Nat.pow_pos (by norm_num)
        have hm : 2 ^ s * p ^ j ≤ n := by rw [hn]; exact Nat.mul_le_mul_left _ (by omega)
        have hdvd : t.totient ∣ n - 2 ^ s * p ^ j := by
          rw [hn, ← Nat.mul_sub, hsub]
          exact dvd_mul_left _ _
        have hsm : s ≤ 2 ^ s * p ^ j := by nlinarith
        have := key n s t (2 ^ s * p ^ j) t.totient hn hsm hm hdvd (two_pow_totient t ht)
        have : 3 * (2 ^ s * p ^ j) ≤ n := by rw [hn]; nlinarith
        omega
      · obtain ⟨u, v, huv, hcop, hu, hv⟩ := split t (by omega) hpp
        have huo : Odd u := Odd.of_dvd_nat ht ⟨v, huv⟩
        have hvo : Odd v := Odd.of_dvd_nat ht ⟨u, by rw [huv, mul_comm]⟩
        have hu3 : 3 ≤ u := by
          rcases huo with ⟨c, hc⟩
          omega
        have hv3 : 3 ≤ v := by
          rcases hvo with ⟨c, hc⟩
          omega
        obtain ⟨x, hx⟩ := Nat.totient_even (by omega : 2 < u)
        obtain ⟨y, hy⟩ := Nat.totient_even (by omega : 2 < v)
        have hxu : u.totient < u := Nat.totient_lt u hu
        have hyv : v.totient < v := Nat.totient_lt v hv
        have hxpos : 0 < u.totient := Nat.totient_pos.mpr (by omega)
        have hypos : 0 < v.totient := Nat.totient_pos.mpr (by omega)
        have h1u : 2 ^ (2 * x * y) ≡ 1 [MOD u] := by
          have := (two_pow_totient u huo).pow y
          rw [← pow_mul, one_pow, hx] at this
          convert this using 2
          ring
        have h1v : 2 ^ (2 * x * y) ≡ 1 [MOD v] := by
          have := (two_pow_totient v hvo).pow x
          rw [← pow_mul, one_pow, hy] at this
          convert this using 2
          ring
        have h1t : 2 ^ (2 * x * y) ≡ 1 [MOD t] := by
          rw [huv]
          exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1u, h1v⟩
        have hDpos : 0 < 2 * x * y := by
          have : 0 < x := by omega
          have : 0 < y := by omega
          positivity
        have hDlt : 2 * (2 * x * y) + 1 ≤ t := by
          rw [huv]
          have h1 : 2 * x + 1 ≤ u := by omega
          have h2 : 2 * y + 1 ≤ v := by omega
          nlinarith [Nat.mul_le_mul h1 h2]
        obtain ⟨h5, h6⟩ := key_mod n s t (2 * x * y) hn hsn hDpos h1t
        rcases Nat.eq_zero_or_pos s with rfl | hs0
        · rw [pow_zero, one_mul] at hn
          rw [Nat.sub_zero] at h5 h6
          have hq : 2 ≤ n / (2 * x * y) := (Nat.le_div_iff_mul_le hDpos).mpr (by omega)
          have hdm := Nat.div_add_mod n (2 * x * y)
          have hmul := Nat.mul_le_mul_left (2 * x * y) hq
          omega
        · have : s = 1 := by omega
          subst this
          rw [pow_one] at hn
          omega
    · obtain ⟨h5, h6⟩ := key_mod n s t t.totient hn hsn (Nat.totient_pos.mpr ht0)
        (two_pow_totient t ht)
      have h7 : t.totient < t := Nat.totient_lt t (by omega)
      have h4 : 4 ≤ 2 ^ s := by
        have : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs2
        omega
      have h8' : 3 * s + 3 * t ≤ 2 ^ s * t + 6 := by nlinarith
      omega

end OMA.A270096

theorem OMA.solution : type_of% @OMA.S_oeis_a270096.main :=
  fun n h => OMA.A270096.bound n h
