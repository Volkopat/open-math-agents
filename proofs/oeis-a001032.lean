import OMAStatements.S_oeis_a001032
import Mathlib

-- Problem: A001032: Numbers k such that sum of squares of k consecutive integers >= 1 is a square.
-- Upstream: statements/oeis-a001032.lean (declaration OMA.S_oeis_a001032.main)
-- Credit: @theterabites
--
-- Ralf Stephan's observation: every term is 0, 1, 2, 9, 11, 16 or 23 modulo 24.
-- With t = 2m + k - 1 the sum S of k consecutive squares from m satisfies 12 S = k (3 t^2 + k^2 - 1),
-- so 12 r^2 = k (3 t^2 + k^2 - 1) and 3 (4 r^2 - k t^2) = (k - 1) k (k + 1). Then:
-- * k = 4, 5, 6 mod 8: a congruence modulo 4 (checked by decide over ZMod 24);
-- * k = 10, 18 mod 24: k + 1 is 3 mod 8, so some prime q = 3 mod 4 divides it to an odd power;
--   descent on 4 r^2 - k t^2 makes -1 a square mod q (Thomas Andrews, condition 2b);
-- * k = 8, 17 mod 24: the same with (k + 1) / 3, which is 3 or 6 mod 8 (condition 2a);
-- * k = 7, 19 mod 24: every prime with odd exponent in k has 3 as a square, hence is +-1 mod 12
--   by quadratic reciprocity, so k would be +-1 mod 12 (condition 1d);
-- * k = 3, 15 mod 24: the 3-adic part is an odd power of 3 with cofactor 2 mod 3 (condition 1c),
--   and the cofactor is +-1 mod 12 as above, contradicting k = 3, 7 mod 8.

namespace OMA.A001032Proof

open Finset

/-! ## The closed forms of the sum of squares -/

lemma sum12 (m k : ℕ) :
    (12 : ℤ) * ∑ i ∈ range k, ((m : ℤ) + i) ^ 2 =
      (k : ℤ) * (3 * (2 * (m : ℤ) + k - 1) ^ 2 + (k : ℤ) ^ 2 - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

lemma sum6 (m k : ℕ) :
    (6 : ℤ) * ∑ i ∈ range k, ((m : ℤ) + i) ^ 2 =
      6 * (k : ℤ) * (m : ℤ) ^ 2 + 6 * (k : ℤ) * ((k : ℤ) - 1) * m +
        (k : ℤ) * ((k : ℤ) - 1) * (2 * (k : ℤ) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

/-! ## The residues 4, 5, 6 modulo 8: a congruence modulo 4 -/

set_option maxRecDepth 100000 in
lemma zmod24_key : ∀ a b c : ZMod 24,
    6 * c ^ 2 = 6 * a * b ^ 2 + 6 * a * (a - 1) * b + a * (a - 1) * (2 * a - 1) →
    a.val % 8 ≠ 4 ∧ a.val % 8 ≠ 5 ∧ a.val % 8 ≠ 6 := by
  decide

lemma mod_part (k m r : ℤ)
    (h : 6 * r ^ 2 = 6 * k * m ^ 2 + 6 * k * (k - 1) * m + k * (k - 1) * (2 * k - 1)) :
    k % 8 ≠ 4 ∧ k % 8 ≠ 5 ∧ k % 8 ≠ 6 := by
  have h' := congrArg (Int.cast : ℤ → ZMod 24) h
  push_cast at h'
  have hv := ZMod.val_intCast (n := 24) k
  have := zmod24_key _ _ _ h'
  omega

/-! ## Valuation tools -/

lemma sqval {p : ℤ} (hp : Prime p) : ∀ n : ℕ, ∀ r : ℤ,
    p ^ (2 * n + 1) ∣ r ^ 2 → p ^ (2 * n + 2) ∣ r ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro r h
    have : p ∣ r := hp.dvd_of_dvd_pow (by simpa using h)
    obtain ⟨r1, rfl⟩ := this
    exact ⟨r1 ^ 2, by ring⟩
  | succ n ih =>
    intro r h
    have : p ∣ r := hp.dvd_of_dvd_pow ((dvd_pow_self _ (by omega)).trans h)
    obtain ⟨r1, rfl⟩ := this
    have hq0 : p ^ 2 ≠ 0 := pow_ne_zero _ hp.ne_zero
    have e : (p * r1) ^ 2 = p ^ 2 * r1 ^ 2 := by ring
    rw [e, show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by ring, pow_add] at h
    rw [e, show 2 * (n + 1) + 2 = 2 + (2 * n + 2) by ring, pow_add]
    exact mul_dvd_mul_left _ (ih r1 ((mul_dvd_mul_iff_left hq0).mp h))

lemma odd_val {p k n : ℕ} [hp : Fact p.Prime] (hk : k ≠ 0) (h : padicValNat p k = 2 * n + 1) :
    (p : ℤ) ^ (2 * n + 1) ∣ (k : ℤ) ∧ ¬ (p : ℤ) ^ (2 * n + 2) ∣ (k : ℤ) := by
  constructor
  · have := pow_padicValNat_dvd (p := p) (n := k)
    rw [h] at this
    exact_mod_cast this
  · intro hd
    have hd' : p ^ (2 * n + 2) ∣ k := by exact_mod_cast hd
    exact pow_succ_padicValNat_not_dvd hk (by rw [h]; exact hd')

/-! ## Descent at a prime `q ≡ 3 (mod 4)` dividing `k + 1` -/

lemma not_dvd_four {q : ℕ} (hq : q.Prime) (h3 : q % 4 = 3) : ¬ (q : ℤ) ∣ 4 := by
  intro h
  have h' : q ∣ 4 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) h'
  interval_cases q <;> omega

lemma desc_step {q : ℕ} [hq : Fact q.Prime] (h3 : q % 4 = 3) {k D t r : ℤ}
    (hk : (q : ℤ) ∣ k + 1) (hD : (q : ℤ) ∣ D) (h : 4 * r ^ 2 - k * t ^ 2 = D) :
    (q : ℤ) ∣ t ∧ (q : ℤ) ∣ r := by
  have hqt : (q : ℤ) ∣ t := by
    by_contra ht
    have ht0 : (t : ZMod q) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hk' : (k : ZMod q) = -1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k + 1) q).mpr hk
      push_cast at this
      linear_combination this
    have hD' : (D : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd D q).mpr hD
    have h' := congrArg (Int.cast : ℤ → ZMod q) h
    push_cast at h'
    rw [hk', hD'] at h'
    have e : (t : ZMod q) * (t : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ ht0
    have hsq : IsSquare (-1 : ZMod q) := ⟨2 * r * (t : ZMod q)⁻¹, by
      linear_combination (-((t : ZMod q)⁻¹) ^ 2) * h' + ((t : ZMod q) * (t : ZMod q)⁻¹ + 1) * e⟩
    exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) h3
  refine ⟨hqt, ?_⟩
  have hpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
  have h4 : (q : ℤ) ∣ 4 * r ^ 2 := by
    have : 4 * r ^ 2 = D + k * t ^ 2 := by linarith
    rw [this]
    exact dvd_add hD (dvd_mul_of_dvd_right (dvd_pow hqt two_ne_zero) k)
  rcases hpr.dvd_or_dvd h4 with h | h
  · exact absurd h (not_dvd_four hq.out h3)
  · exact hpr.dvd_of_dvd_pow h

lemma desc {q : ℕ} [hq : Fact q.Prime] (h3 : q % 4 = 3) {k : ℤ} (hk : (q : ℤ) ∣ k + 1) :
    ∀ n : ℕ, ∀ D t r : ℤ, (q : ℤ) ^ (2 * n + 1) ∣ D → ¬ (q : ℤ) ^ (2 * n + 2) ∣ D →
      4 * r ^ 2 - k * t ^ 2 = D → False := by
  intro n
  induction n with
  | zero =>
    intro D t r h1 h2 h
    obtain ⟨⟨t1, rfl⟩, ⟨r1, rfl⟩⟩ := desc_step h3 hk (by simpa using h1) h
    apply h2
    exact ⟨4 * r1 ^ 2 - k * t1 ^ 2, by rw [← h]; ring⟩
  | succ n ih =>
    intro D t r h1 h2 h
    have hqD : (q : ℤ) ∣ D := (dvd_pow_self _ (by omega)).trans h1
    obtain ⟨⟨t1, rfl⟩, ⟨r1, rfl⟩⟩ := desc_step h3 hk hqD h
    have hD : D = (q : ℤ) ^ 2 * (4 * r1 ^ 2 - k * t1 ^ 2) := by rw [← h]; ring
    have hq0 : (q : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.out.ne_zero)
    apply ih (4 * r1 ^ 2 - k * t1 ^ 2) t1 r1
    · rw [hD, show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by ring, pow_add] at h1
      exact (mul_dvd_mul_iff_left hq0).mp h1
    · intro h'
      apply h2
      rw [hD, show 2 * (n + 1) + 2 = 2 + (2 * n + 2) by ring, pow_add]
      exact mul_dvd_mul_left _ h'
    · rfl

/-! ## At a prime dividing `k` to an odd power, `3` is a square -/

lemma three_sq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) {k t r : ℤ} (n : ℕ)
    (h1 : (p : ℤ) ^ (2 * n + 1) ∣ k) (h2 : ¬ (p : ℤ) ^ (2 * n + 2) ∣ k)
    (h : 12 * r ^ 2 = k * (3 * t ^ 2 + k ^ 2 - 1)) : IsSquare (3 : ZMod p) := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpk : (p : ℤ) ∣ k := (dvd_pow_self _ (by omega)).trans h1
  by_cases hF : (p : ℤ) ∣ 3 * t ^ 2 + k ^ 2 - 1
  · have hF' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hF
    have hk' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpk
    push_cast at hF'
    rw [hk'] at hF'
    exact ⟨3 * t, by linear_combination (-3 : ZMod p) * hF'⟩
  · exfalso
    have h12 : ¬ (p : ℤ) ∣ 12 := by
      intro h12
      have hd : p ∣ 2 ^ 2 * 3 := by exact_mod_cast h12
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
          (hp.out.dvd_of_dvd_pow h))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h)
    have hA : (p : ℤ) ^ (2 * n + 1) ∣ r ^ 2 :=
      hpr.pow_dvd_of_dvd_mul_left _ h12 (by rw [h]; exact dvd_mul_of_dvd_left h1 _)
    have hB := sqval hpr n r hA
    exact h2 (hpr.pow_dvd_of_dvd_mul_right _ hF (by rw [← h]; exact dvd_mul_of_dvd_right hB _))

lemma key3 : ∀ x r : ZMod 3, x = r * r → x.val = 0 ∨ x.val = 1 := by decide

/-- Quadratic reciprocity: `3` is a square modulo a prime `p > 3` only if `p ≡ ±1 (mod 12)`. -/
lemma mod12_of_three_sq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : IsSquare (3 : ZMod p)) : p % 12 = 1 ∨ p % 12 = 11 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3' : p % 3 ≠ 0 := by
    intro h0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have h' : IsSquare ((3 : ℕ) : ZMod p) := by exact_mod_cast h
  have hval : ((p : ZMod 3)).val = p % 3 := ZMod.val_natCast 3 p
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h4 | h4
  · obtain ⟨r, hr⟩ :=
      (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h4 (by norm_num : (3 : ℕ) ≠ 2)).mp h'
    have := key3 _ r hr
    omega
  · have hns := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 (by norm_num) hp3).mp h'
    have hne1 : p % 3 ≠ 1 := by
      intro h1
      apply hns
      refine ⟨1, ?_⟩
      rw [mul_one, ← ZMod.natCast_mod, h1, Nat.cast_one]
    omega

/-- A number coprime to `6` all of whose odd-exponent primes are `≡ ±1 (mod 12)` is itself
`≡ ±1 (mod 12)`. -/
lemma mod12_prod : ∀ n : ℕ, Nat.Coprime n 6 →
    (∀ p : ℕ, p.Prime → Odd (padicValNat p n) → p % 12 = 1 ∨ p % 12 = 11) →
    n % 12 = 1 ∨ n % 12 = 11 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hcop hodd
  by_cases hn1 : n = 1
  · left; subst hn1; rfl
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp [Nat.Coprime] at hcop
  obtain ⟨p, hp, hpn⟩ : ∃ p, p.Prime ∧ p ∣ n := ⟨n.minFac, Nat.minFac_prime hn1, Nat.minFac_dvd n⟩
  have := Fact.mk hp
  obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hnm; exact hn0 hnm
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hnm
    exact hpm (hnm ▸ hpn)
  have hpc : Nat.Coprime p 6 := Nat.Coprime.coprime_dvd_left hpn hcop
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hpc
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hpc
  have hmlt : m < n := by
    rw [hnm]
    have : 1 < p ^ a := Nat.one_lt_pow ha hp.one_lt
    have : 0 < m := Nat.pos_of_ne_zero hm0
    nlinarith
  have hmcop : Nat.Coprime m 6 :=
    Nat.Coprime.coprime_dvd_left (hnm ▸ Dvd.intro_left _ rfl) hcop
  have hmodd : ∀ q : ℕ, q.Prime → Odd (padicValNat q m) → q % 12 = 1 ∨ q % 12 = 11 := by
    intro q hq hqo
    have := Fact.mk hq
    by_cases hqp : q = p
    · subst hqp
      rw [padicValNat.eq_zero_of_not_dvd hpm] at hqo
      exact absurd hqo (by decide)
    · apply hodd q hq
      rw [hnm, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.eq_zero_of_not_dvd,
        zero_add]
      · exact hqo
      · intro hd
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd))
  have hm12 := ih m hmlt hmcop hmodd
  have hvp : padicValNat p n = a := by
    rw [hnm, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hpm, add_zero]
  have hp12 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
    have h2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have h3 : p % 3 ≠ 0 := by
      intro h0
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
    omega
  have hsq : p ^ 2 % 12 = 1 := by
    rcases hp12 with h | h | h | h <;> simp [Nat.pow_mod, h]
  have hpa : p ^ a % 12 = 1 ∨ p ^ a % 12 = 11 := by
    rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      rw [hb, ← two_mul, pow_mul, Nat.pow_mod, hsq, one_pow]
      norm_num
    · have hpo := hodd p hp (by rw [hvp]; exact ⟨b, hb⟩)
      rw [hb, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, hsq, one_pow]
      rcases hpo with h | h <;> simp [h]
  rw [hnm, Nat.mul_mod]
  rcases hpa with h | h <;> rcases hm12 with h' | h' <;> simp [h, h']

/-- The `3`-adic part of `k`: an odd power of `3`, with cofactor `≡ 2 (mod 3)`. -/
lemma three_adic {e k' : ℕ} (he : 1 ≤ e) (h3 : ¬ 3 ∣ k') {K t r : ℤ}
    (hK : K = 3 ^ e * k') (h : 12 * r ^ 2 = K * (3 * t ^ 2 + K ^ 2 - 1)) :
    Odd e ∧ k' % 3 = 2 := by
  have hpr3 : Prime (3 : ℤ) := Int.prime_three
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  have h30 : (3 : ZMod 3) = 0 := rfl
  have hK3 : (K : ZMod 3) = 0 := by
    rw [hK]; push_cast; rw [h30, zero_pow (Nat.succ_ne_zero f), zero_mul]
  have hFz : ((3 * t ^ 2 + K ^ 2 - 1 : ℤ) : ZMod 3) = 2 := by
    push_cast
    rw [hK3]
    linear_combination ((t : ZMod 3) ^ 2 - 1) * h30
  have h3F : ¬ (3 : ℤ) ∣ 3 * t ^ 2 + K ^ 2 - 1 := by
    intro hd
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
    rw [hFz] at this
    exact absurd this (by decide)
  have h3k' : ¬ (3 : ℤ) ∣ (k' : ℤ) := by exact_mod_cast h3
  have h4 : 4 * r ^ 2 = 3 ^ f * (k' * (3 * t ^ 2 + K ^ 2 - 1)) := by
    have : (3 : ℤ) * (4 * r ^ 2) = 3 * (3 ^ f * (k' * (3 * t ^ 2 + K ^ 2 - 1))) := by
      calc (3 : ℤ) * (4 * r ^ 2) = 12 * r ^ 2 := by ring
        _ = K * (3 * t ^ 2 + K ^ 2 - 1) := h
        _ = _ := by rw [hK]; ring
    exact mul_left_cancel₀ (by norm_num) this
  have h34 : ¬ (3 : ℤ) ∣ 4 := by norm_num
  rcases Nat.even_or_odd f with ⟨n, hn⟩ | ⟨n, hn⟩
  · refine ⟨⟨n, by omega⟩, ?_⟩
    have hdiv : ((3 : ℤ) ^ n) ^ 2 ∣ r ^ 2 := by
      have : (3 : ℤ) ^ f ∣ 4 * r ^ 2 := ⟨_, h4⟩
      rw [← pow_mul, show n * 2 = f by omega]
      exact hpr3.pow_dvd_of_dvd_mul_left f h34 this
    obtain ⟨s, rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hdiv
    have h4' : 4 * s ^ 2 = k' * (3 * t ^ 2 + K ^ 2 - 1) := by
      have : (3 : ℤ) ^ f * (4 * s ^ 2) = 3 ^ f * (k' * (3 * t ^ 2 + K ^ 2 - 1)) := by
        rw [← h4, hn]; ring
      exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) this
    have hz := congrArg (Int.cast : ℤ → ZMod 3) h4'
    rw [Int.cast_mul (k' : ℤ) (3 * t ^ 2 + K ^ 2 - 1), hFz] at hz
    push_cast at hz
    have hk'z : ((k' : ℕ) : ZMod 3) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact h3
    have key : ∀ x y : ZMod 3, y ≠ 0 → 4 * x ^ 2 = y * 2 → y.val = 2 := by decide
    have := key _ _ hk'z hz
    rwa [ZMod.val_natCast] at this
  · exfalso
    have hA : (3 : ℤ) ^ (2 * n + 1) ∣ r ^ 2 := by
      rw [← hn]; exact hpr3.pow_dvd_of_dvd_mul_left f h34 ⟨_, h4⟩
    have hB := sqval hpr3 n r hA
    have : (3 : ℤ) ^ (2 * n + 1) * 3 ∣ (3 : ℤ) ^ (2 * n + 1) * (k' * (3 * t ^ 2 + K ^ 2 - 1)) := by
      rw [← pow_succ, ← hn, ← h4]
      exact dvd_mul_of_dvd_right (by rw [hn]; exact hB) 4
    have h3kF := (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp this
    rcases hpr3.dvd_or_dvd h3kF with h | h
    · exact h3k' h
    · exact h3F h

/-! ## The residue classes -/

lemma odd_prime_mod12 {k p : ℕ} (hk0 : k ≠ 0) (hp : p.Prime) (hodd : Odd (padicValNat p k))
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {T r : ℤ}
    (E : 12 * r ^ 2 = (k : ℤ) * (3 * T ^ 2 + (k : ℤ) ^ 2 - 1)) : p % 12 = 1 ∨ p % 12 = 11 := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hodd
  obtain ⟨h1, h2⟩ := odd_val hk0 hn
  exact mod12_of_three_sq hp2 hp3 (three_sq hp2 hp3 n h1 h2 E)

lemma groupA (k : ℕ) (hk : k % 12 = 7) {T r : ℤ}
    (E : 12 * r ^ 2 = (k : ℤ) * (3 * T ^ 2 + (k : ℤ) ^ 2 - 1)) : False := by
  have hk0 : k ≠ 0 := by omega
  have hcop : Nat.Coprime k 6 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    have : k % 6 = 1 := by omega
    rw [this]; rfl
  have := mod12_prod k hcop (fun p hp hodd => by
    have hpk : p ∣ k := dvd_of_one_le_padicValNat (by obtain ⟨n, hn⟩ := hodd; omega)
    refine odd_prime_mod12 hk0 hp hodd ?_ ?_ E
    · rintro rfl; omega
    · rintro rfl; omega)
  omega

lemma groupB (k : ℕ) (h3 : k % 3 = 0) (h8 : k % 8 = 3 ∨ k % 8 = 7) {T r : ℤ}
    (E : 12 * r ^ 2 = (k : ℤ) * (3 * T ^ 2 + (k : ℤ) ^ 2 - 1)) : False := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨e, k', hk', hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 3 (by norm_num)
  have hk'0 : k' ≠ 0 := by rintro rfl; simp at hk; exact hk0 hk
  have he : 1 ≤ e := by
    by_contra he
    push Not at he
    interval_cases e
    simp at hk
    exact hk' (hk ▸ Nat.dvd_of_mod_eq_zero h3)
  have hK : (k : ℤ) = 3 ^ e * k' := by rw [hk]; push_cast; ring
  obtain ⟨hodd_e, hk'3⟩ := three_adic he hk' hK E
  have hk'odd : k' % 2 = 1 := by
    by_contra hc
    have h2 : 2 ∣ k' := by omega
    have : 2 ∣ k := hk ▸ Dvd.dvd.mul_left h2 _
    omega
  have hcop : Nat.Coprime k' 6 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    have : k' % 6 = 5 := by omega
    rw [this]; rfl
  have hm := mod12_prod k' hcop (fun p hp hodd => by
    have := Fact.mk hp
    have hpk' : p ∣ k' := dvd_of_one_le_padicValNat (by obtain ⟨n, hn⟩ := hodd; omega)
    have hp2 : p ≠ 2 := by rintro rfl; omega
    have hp3 : p ≠ 3 := by rintro rfl; exact hk' hpk'
    have hv : padicValNat p k = padicValNat p k' := by
      rw [hk, padicValNat.mul (pow_ne_zero _ (by norm_num)) hk'0, padicValNat.eq_zero_of_not_dvd,
        zero_add]
      intro hd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd))
    exact odd_prime_mod12 hk0 hp (by rw [hv]; exact hodd) hp2 hp3 E)
  have h3e : 3 ^ e % 8 = 3 := by
    obtain ⟨j, rfl⟩ := hodd_e
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have : k % 8 = (3 * (k' % 8)) % 8 := by rw [hk, Nat.mul_mod, h3e]
  omega

lemma no_sum_two_sq {N : ℕ} (h : N % 8 = 3 ∨ N % 8 = 6 ∨ N % 8 = 7) :
    ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, rfl⟩
  have key : ∀ a b : Fin 8, ((a : ℕ) ^ 2 + (b : ℕ) ^ 2) % 8 ≠ 3 ∧
      ((a : ℕ) ^ 2 + (b : ℕ) ^ 2) % 8 ≠ 6 ∧ ((a : ℕ) ^ 2 + (b : ℕ) ^ 2) % 8 ≠ 7 := by decide
  have hk := key ⟨x % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨y % 8, Nat.mod_lt _ (by norm_num)⟩
  have e : (x ^ 2 + y ^ 2) % 8 = ((x % 8) ^ 2 + (y % 8) ^ 2) % 8 := by
    simp [Nat.add_mod, Nat.pow_mod]
  simp only at hk
  omega

lemma qkk {q : ℕ} (hq : q.Prime) (h3 : q % 4 = 3) {k : ℤ} (h1 : (q : ℤ) ∣ k + 1)
    (h2 : (q : ℤ) ∣ k * (k - 1)) : False := by
  have hpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rcases hpr.dvd_or_dvd h2 with h | h
  · have h' := dvd_sub h1 h
    rw [add_sub_cancel_left] at h'
    exact hpr.not_isUnit (isUnit_of_dvd_one h')
  · have h' := dvd_sub h1 h
    rw [show k + 1 - (k - 1) = 2 by ring] at h'
    have : q ∣ 2 := by exact_mod_cast h'
    have := Nat.le_of_dvd (by norm_num) this
    omega

lemma case_q (k : ℕ) {N : ℕ} (hN : N ∣ k + 1) (hN0 : N ≠ 0) (hsq : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2)
    {u T r : ℤ} (hu : ∀ q : ℕ, q.Prime → q % 4 = 3 → (q : ℤ) ∣ (k : ℤ) + 1 → ¬ (q : ℤ) ∣ u)
    (hD : 4 * r ^ 2 - (k : ℤ) * T ^ 2 = u * N) : False := by
  rw [Nat.eq_sq_add_sq_iff] at hsq
  push Not at hsq
  obtain ⟨q, hqN, hq3, hqodd⟩ := hsq
  have hq := Nat.prime_of_mem_primeFactors hqN
  have := Fact.mk hq
  rw [Nat.not_even_iff_odd] at hqodd
  obtain ⟨n, hn⟩ := hqodd
  obtain ⟨h1, h2⟩ := odd_val hN0 hn
  have hqk : (q : ℤ) ∣ (k : ℤ) + 1 := by
    have : q ∣ k + 1 := (Nat.dvd_of_mem_primeFactors hqN).trans hN
    exact_mod_cast this
  have hpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  refine desc hq3 hqk n (u * N) T r (dvd_mul_of_dvd_right h1 u) ?_ hD
  intro hd
  exact h2 (hpr.pow_dvd_of_dvd_mul_left _ (hu q hq hq3 hqk) hd)

lemma groupC (k : ℕ) (h8 : (k + 1) % 8 = 3) (h3 : k % 3 ≠ 2) {T r : ℤ}
    (E3 : 3 * (4 * r ^ 2 - (k : ℤ) * T ^ 2) = (k : ℤ) * ((k : ℤ) - 1) * ((k : ℤ) + 1)) : False := by
  have h3d : (3 : ℤ) ∣ (k : ℤ) * ((k : ℤ) - 1) := by
    rcases (show k % 3 = 0 ∨ k % 3 = 1 by omega) with h | h
    · exact dvd_mul_of_dvd_left (by omega) _
    · exact dvd_mul_of_dvd_right (by omega) _
  obtain ⟨u, hu⟩ := h3d
  refine case_q k (N := k + 1) dvd_rfl (by omega) (no_sum_two_sq (by omega)) (u := u) (T := T)
    (r := r) ?_ ?_
  · intro q hq hq3 hqk hqu
    exact qkk hq hq3 hqk (by rw [hu]; exact dvd_mul_of_dvd_right hqu 3)
  · have : 3 * (4 * r ^ 2 - (k : ℤ) * T ^ 2) = 3 * (u * ((k + 1 : ℕ) : ℤ)) := by
      rw [E3]; push_cast; linear_combination ((k : ℤ) + 1) * hu
    exact mul_left_cancel₀ (by norm_num) this

lemma groupD (k : ℕ) (h3 : k % 3 = 2) (h8 : ((k + 1) / 3) % 8 = 3 ∨ ((k + 1) / 3) % 8 = 6)
    {T r : ℤ}
    (E3 : 3 * (4 * r ^ 2 - (k : ℤ) * T ^ 2) = (k : ℤ) * ((k : ℤ) - 1) * ((k : ℤ) + 1)) : False := by
  have hM : ((((k + 1) / 3 : ℕ)) : ℤ) * 3 = (k : ℤ) + 1 := by
    have : (k + 1) / 3 * 3 = k + 1 := by omega
    exact_mod_cast this
  refine case_q k (N := (k + 1) / 3) (Nat.div_dvd_of_dvd (by omega)) (by omega)
    (no_sum_two_sq (by omega)) (u := (k : ℤ) * ((k : ℤ) - 1)) (T := T) (r := r) ?_ ?_
  · intro q hq hq3 hqk hqu
    exact qkk hq hq3 hqk hqu
  · have : 3 * (4 * r ^ 2 - (k : ℤ) * T ^ 2) =
        3 * ((k : ℤ) * ((k : ℤ) - 1) * (((k + 1) / 3 : ℕ) : ℤ)) := by
      rw [E3]; linear_combination (-((k : ℤ) * ((k : ℤ) - 1))) * hM
    exact mul_left_cancel₀ (by norm_num) this

theorem main_proof : ∀ k : ℕ, OMA.S_oeis_a001032.InA001032 k →
    k % 24 ∈ ({0, 1, 2, 9, 11, 16, 23} : Finset ℕ) := by
  rintro k ⟨hk0, m, r, hm0, hsum⟩
  have hS : (∑ i ∈ range k, ((m : ℤ) + i) ^ 2) = (r : ℤ) ^ 2 := by exact_mod_cast hsum
  have E12 : 12 * (r : ℤ) ^ 2 = (k : ℤ) * (3 * (2 * (m : ℤ) + k - 1) ^ 2 + (k : ℤ) ^ 2 - 1) := by
    rw [← hS]; exact sum12 m k
  have E6 : 6 * (r : ℤ) ^ 2 = 6 * (k : ℤ) * (m : ℤ) ^ 2 + 6 * (k : ℤ) * ((k : ℤ) - 1) * m +
      (k : ℤ) * ((k : ℤ) - 1) * (2 * (k : ℤ) - 1) := by
    rw [← hS]; exact sum6 m k
  have E3 : 3 * (4 * (r : ℤ) ^ 2 - (k : ℤ) * (2 * (m : ℤ) + k - 1) ^ 2) =
      (k : ℤ) * ((k : ℤ) - 1) * ((k : ℤ) + 1) := by linear_combination E12
  have hmod := mod_part (k : ℤ) m r E6
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ : ∃ j, k % 24 = j := ⟨_, rfl⟩
  have hj24 : j < 24 := hj ▸ Nat.mod_lt _ (by norm_num)
  interval_cases j <;> first
    | omega
    | exact groupA k (by omega) E12
    | exact groupB k (by omega) (by omega) E12
    | exact groupC k (by omega) (by omega) E3
    | exact groupD k (by omega) (by omega) E3

end OMA.A001032Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a001032.main := by
  exact OMA.A001032Proof.main_proof
