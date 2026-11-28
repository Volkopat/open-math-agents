import OMAStatements.S_oeis_a145047

namespace OMA.S_oeis_a145047



theorem good_self (p : ℕ) : Good p p := by
  unfold Good
  rw [show p * p = p ^ 2 by ring, Nat.sqrt_eq' p, Nat.sub_self]
  exact ⟨0, rfl⟩

/-- The descent step: a common prime factor of `a` and `b` gives a smaller good `s`. -/
theorem descent {p s r a b : ℕ} (hp : p.Prime) (hs : 0 < s) (hsp : s < p) (hr : r.Prime)
    (ha : a = Nat.sqrt (s * p)) (hab : s * p = a ^ 2 + b ^ 2) (hra : r ∣ a) (hrb : r ∣ b) :
    ∃ t, 0 < t ∧ t < s ∧ Good p t := by
  obtain ⟨a', rfl⟩ := hra
  obtain ⟨b', rfl⟩ := hrb
  have hr2 : r ^ 2 ∣ s * p := ⟨a' ^ 2 + b' ^ 2, by rw [hab]; ring⟩
  have hrp : r ≠ p := by
    rintro rfl
    have : r ∣ s := by
      have h1 : r * r ∣ s * r := by rw [← sq]; exact hr2
      have := Nat.dvd_of_mul_dvd_mul_right hr.pos h1
      exact this
    have := Nat.le_of_dvd hs this
    omega
  have hcop : Nat.Coprime (r ^ 2) p :=
    Nat.Coprime.pow_left 2 ((Nat.coprime_primes hr hp).mpr hrp)
  have hrs : r ^ 2 ∣ s := hcop.dvd_of_dvd_mul_right hr2
  obtain ⟨t, rfl⟩ := hrs
  have hr1 : 1 < r ^ 2 := by
    have := hr.two_le
    nlinarith
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; simp at hs
    · exact h
  have htp : t * p = a' ^ 2 + b' ^ 2 := by
    have h1 : r ^ 2 * (t * p) = r ^ 2 * (a' ^ 2 + b' ^ 2) := by
      rw [← mul_assoc, hab]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  -- ⌊√(t p)⌋ = a'
  have hsq : Nat.sqrt (t * p) = a' := by
    have h1 := Nat.sqrt_le' (r ^ 2 * t * p)
    have h2 := Nat.lt_succ_sqrt' (r ^ 2 * t * p)
    rw [← ha] at h1 h2
    symm
    rw [Nat.eq_sqrt]
    have hrpos : 0 < r := hr.pos
    constructor
    · have : r ^ 2 * (a' * a') ≤ r ^ 2 * (t * p) := by nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    · have h3 : r ^ 2 * (t * p) < r ^ 2 * ((a' + 1) * (a' + 1)) := by
        have : (r * a' + 1) ^ 2 ≤ (r * (a' + 1)) ^ 2 := by
          apply Nat.pow_le_pow_left
          nlinarith
        nlinarith
      exact Nat.lt_of_mul_lt_mul_left h3
  refine ⟨t, ht, ?_, ?_⟩
  · calc t = 1 * t := (one_mul t).symm
      _ < r ^ 2 * t := Nat.mul_lt_mul_of_pos_right hr1 ht
  · unfold Good
    rw [hsq, htp, Nat.add_sub_cancel_left]
    exact ⟨b', sq b'⟩

theorem least_in_A008784 (p s : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (hs : 0 < s) (hgood : Good p s)
    (hmin : ∀ t, 0 < t → t < s → ¬ Good p t) : InA008784 s := by
  have := Fact.mk hp
  by_cases hps : p ≤ s
  · have hs' : s = p := by
      by_contra hne
      exact hmin p hp.pos (lt_of_le_of_ne hps (Ne.symm hne)) (good_self p)
    subst hs'
    unfold InA008784
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  · rw [not_le] at hps
    obtain ⟨b, hb⟩ := hgood
    set a := Nat.sqrt (s * p) with ha
    have hle : a ^ 2 ≤ s * p := Nat.sqrt_le' (s * p)
    have hab : s * p = a ^ 2 + b ^ 2 := by
      rw [sq b, ← hb]
      omega
    have hcop : Nat.Coprime a b := by
      apply Nat.coprime_of_dvd
      intro r hr hra hrb
      obtain ⟨t, ht, hts, hgt⟩ := descent hp hs hps hr ha hab hra hrb
      exact hmin t ht hts hgt
    have hsq := ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime
      (n := ((s * p : ℕ) : ℤ)) (x := (a : ℤ)) (y := (b : ℤ)) (by rw [hab]; push_cast; ring)
      (Nat.isCoprime_iff_coprime.mpr hcop)
    rw [Int.natAbs_natCast] at hsq
    exact ZMod.isSquare_neg_one_of_dvd (Dvd.intro p rfl) hsq

theorem solution : ∀ p s : ℕ, p.Prime → p % 4 = 1 → 0 < s → Good p s →
    (∀ t, 0 < t → t < s → ¬ Good p t) → InA008784 s :=
  least_in_A008784

/-! Control: for p = 1237, the first term of the entry, s = 1, ..., 9 fail and s = 10 works. -/

theorem not_good_of {p t r v : ℕ} (hr : r * r ≤ t * p ∧ t * p < (r + 1) * (r + 1))
    (hv : t * p - r ^ 2 = v) (hns : ∀ m, m ≤ v → m * m ≠ v) : ¬ Good p t := by
  unfold Good
  rw [show Nat.sqrt (t * p) = r from (Nat.eq_sqrt.mpr hr).symm, hv]
  rintro ⟨m, hm⟩
  exact hns m (by nlinarith) hm.symm

theorem control_1237 : Good 1237 10 ∧ ∀ t, 0 < t → t < 10 → ¬ Good 1237 t := by
  refine ⟨?_, ?_⟩
  · unfold Good
    rw [show Nat.sqrt (10 * 1237) = 111 from (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩).symm]
    exact ⟨7, by norm_num⟩
  · intro t ht ht10
    interval_cases t
    · exact not_good_of (r := 35) (v := 12) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)
    · exact not_good_of (r := 49) (v := 73) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)
    · exact not_good_of (r := 60) (v := 111) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)
    · exact not_good_of (r := 70) (v := 48) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)
    · exact not_good_of (r := 78) (v := 101) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)
    · exact not_good_of (r := 86) (v := 26) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)
    · exact not_good_of (r := 93) (v := 10) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)
    · exact not_good_of (r := 99) (v := 95) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)
    · exact not_good_of (r := 105) (v := 108) ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide)

end OMA.S_oeis_a145047

theorem OMA.solution : type_of% @OMA.S_oeis_a145047.main :=
  OMA.S_oeis_a145047.solution
