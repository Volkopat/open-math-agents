import OMAStatements.S_oeis_a283754
import Mathlib

open OMA.S_oeis_a283754


theorem cop (n : ℕ) : Nat.Coprime (2 ^ n) (3 ^ n) := Nat.Coprime.pow n n (by norm_num)

theorem one_lt3 (n : ℕ) (hn : 1 ≤ n) : 1 < 3 ^ n := Nat.one_lt_pow (by omega) (by norm_num)

theorem six_pow (n : ℕ) : 6 ^ n = 2 ^ n * 3 ^ n := by rw [← Nat.mul_pow]

theorem a_spec (n : ℕ) (hn : 1 ≤ n) : a n * 2 ^ n % 3 ^ n = 1 ∧ a n < 3 ^ n := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime (cop n) (one_lt3 n hn)
  have hmem : m ∈ {k : ℕ | k * 2 ^ n % 3 ^ n = 1} := by
    show m * 2 ^ n % 3 ^ n = 1
    rw [mul_comm]; exact hm
  have hs : a n * 2 ^ n % 3 ^ n = 1 := Nat.sInf_mem ⟨m, hmem⟩
  refine ⟨hs, ?_⟩
  have hmod : a n % 3 ^ n ∈ {k : ℕ | k * 2 ^ n % 3 ^ n = 1} := by
    show a n % 3 ^ n * 2 ^ n % 3 ^ n = 1
    rw [Nat.mod_mul_mod]; exact hs
  have hle : a n ≤ a n % 3 ^ n := Nat.sInf_le hmod
  have h3 : a n % 3 ^ n < 3 ^ n := Nat.mod_lt _ (by positivity)
  omega

theorem a_eq (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k * 2 ^ n % 3 ^ n = 1) (hk3 : k < 3 ^ n) :
    a n = k := by
  obtain ⟨hs, hlt⟩ := a_spec n hn
  have hmod : a n * 2 ^ n ≡ k * 2 ^ n [MOD 3 ^ n] := by
    unfold Nat.ModEq; rw [hs, hk]
  have h2 : a n ≡ k [MOD 3 ^ n] := Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.symm (cop n)) hmod
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hk3] at h2

theorem idem_struct (n : ℕ) (hn : 1 ≤ n) (x : ℕ) (hx6 : x < 6 ^ n) (hx4 : x % 6 = 4)
    (hid : x ^ 2 % 6 ^ n = x % 6 ^ n) : x = 2 ^ n * a n := by
  have hdvd : 6 ^ n ∣ x * (x - 1) := by
    have hle : x ≤ x ^ 2 := by nlinarith
    have := (Nat.modEq_iff_dvd' hle).1 (Nat.ModEq.symm hid)
    have e : x ^ 2 - x = x * (x - 1) := by rw [Nat.mul_sub_one, sq]
    rwa [e] at this
  rw [six_pow] at hdvd
  have h2 : 2 ^ n ∣ x := by
    have hd2 : 2 ^ n ∣ x * (x - 1) := Dvd.dvd.trans (Dvd.intro _ rfl) hdvd
    have hc : Nat.Coprime (2 ^ n) (x - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left, Nat.odd_iff]; omega
    exact hc.dvd_of_dvd_mul_right hd2
  have h3 : 3 ^ n ∣ x - 1 := by
    have hd3 : 3 ^ n ∣ x * (x - 1) := Dvd.dvd.trans (Dvd.intro_left _ rfl) hdvd
    have hc : Nat.Coprime (3 ^ n) x := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; omega
    exact hc.dvd_of_dvd_mul_left hd3
  obtain ⟨k, hk⟩ := h2
  obtain ⟨c, hc⟩ := h3
  have hx : x = 3 ^ n * c + 1 := by omega
  have hkmod : k * 2 ^ n % 3 ^ n = 1 := by
    rw [mul_comm, ← hk, hx, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (one_lt3 n hn)
  have hk3 : k < 3 ^ n := by
    rw [six_pow, hk] at hx6
    exact Nat.lt_of_mul_lt_mul_left hx6
  rw [a_eq n hn k hkmod hk3]; exact hk

theorem psum_succ (d : ℕ → ℕ) (n : ℕ) : psum d (n + 1) = psum d n + d n * 6 ^ n :=
  Finset.sum_range_succ _ _

theorem psum_lt (d : ℕ → ℕ) (hd : ∀ i, d i < 6) (n : ℕ) : psum d n < 6 ^ n := by
  induction n with
  | zero => simp [psum]
  | succ n ih =>
    rw [psum_succ, pow_succ]
    have : d n * 6 ^ n ≤ 5 * 6 ^ n := Nat.mul_le_mul_right _ (by have := hd n; omega)
    omega

theorem psum_mod6 (d : ℕ → ℕ) (h0 : d 0 = 4) (n : ℕ) : psum d (n + 1) % 6 = 4 := by
  induction n with
  | zero => simp [psum, h0]
  | succ m ih =>
    rw [psum_succ, pow_succ, show d (m + 1) * (6 ^ m * 6) = (d (m + 1) * 6 ^ m) * 6 by ring,
      Nat.add_mul_mod_self_right]
    exact ih

theorem forward (d : ℕ → ℕ) (hd : IsIdemDigits d) (n : ℕ) (hn : 1 ≤ n) :
    2 * a (n + 1) = a n + d n * 3 ^ n := by
  obtain ⟨hlt, h0, hid⟩ := hd
  have hx : ∀ m, 1 ≤ m → psum d m = 2 ^ m * a m := by
    intro m hm
    apply idem_struct m hm _ (psum_lt d hlt m)
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      exact psum_mod6 d h0 j
    · exact hid m
  have e := psum_succ d n
  rw [hx n hn, hx (n + 1) (by omega), six_pow] at e
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ n by positivity)
  rw [pow_succ] at e
  linarith [e]

noncomputable def xx (n : ℕ) : ℕ := 2 ^ n * a n

theorem a_zero : a 0 = 0 := by
  show sInf {k : ℕ | k * 2 ^ 0 % 3 ^ 0 = 1} = 0
  have : {k : ℕ | k * 2 ^ 0 % 3 ^ 0 = 1} = ∅ := by
    ext k; simp [Nat.mod_one]
  rw [this, Nat.sInf_empty]

theorem xx_lt (n : ℕ) : xx n < 6 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [xx, a_zero]
  · unfold xx; rw [six_pow]
    exact Nat.mul_lt_mul_of_pos_left (a_spec n hn).2 (by positivity)

theorem xx_mod3 (n : ℕ) (hn : 1 ≤ n) : xx n % 3 ^ n = 1 := by
  unfold xx; rw [mul_comm]; exact (a_spec n hn).1

theorem xx_compat (n : ℕ) : xx (n + 1) % 6 ^ n = xx n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.mod_one, xx, a_zero]
  · have h2 : xx (n + 1) ≡ xx n [MOD 2 ^ n] := by
      unfold Nat.ModEq xx
      rw [pow_succ, show 2 ^ n * 2 * a (n + 1) = 2 ^ n * (2 * a (n + 1)) by ring,
        Nat.mul_mod_right, Nat.mul_mod_right]
    have h3 : xx (n + 1) ≡ xx n [MOD 3 ^ n] := by
      unfold Nat.ModEq
      rw [xx_mod3 n hn, ← Nat.mod_mod_of_dvd (xx (n + 1)) (pow_dvd_pow 3 (Nat.le_succ n)),
        xx_mod3 (n + 1) (by omega)]
      exact Nat.mod_eq_of_lt (one_lt3 n hn)
    have h6 := (Nat.modEq_and_modEq_iff_modEq_mul (cop n)).1 ⟨h2, h3⟩
    rw [← six_pow] at h6
    unfold Nat.ModEq at h6
    rw [h6, Nat.mod_eq_of_lt (xx_lt n)]

noncomputable def dd (n : ℕ) : ℕ := xx (n + 1) / 6 ^ n

theorem psum_dd (n : ℕ) : psum dd n = xx n := by
  induction n with
  | zero => simp [psum, xx, a_zero]
  | succ n ih =>
    rw [psum_succ, ih, dd, ← xx_compat n]
    exact Nat.mod_add_div' _ _

theorem exists_d : ∃ d, IsIdemDigits d := by
  refine ⟨dd, ?_, ?_, ?_⟩
  · intro i
    unfold dd
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← pow_succ]
    exact xx_lt (i + 1)
  · have : a 1 = 2 := a_eq 1 le_rfl 2 (by norm_num) (by norm_num)
    simp [dd, xx, this]
  · intro n
    rw [psum_dd]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.mod_one]
    · have h2 : xx n ^ 2 ≡ xx n [MOD 2 ^ n] := by
        unfold Nat.ModEq xx
        rw [mul_pow, show (2 ^ n) ^ 2 * a n ^ 2 = 2 ^ n * (2 ^ n * a n ^ 2) by ring,
          Nat.mul_mod_right, Nat.mul_mod_right]
      have h3 : xx n ^ 2 ≡ xx n [MOD 3 ^ n] := by
        unfold Nat.ModEq
        rw [Nat.pow_mod, xx_mod3 n hn]
        simp [Nat.mod_eq_of_lt (one_lt3 n hn)]
      have h6 := (Nat.modEq_and_modEq_iff_modEq_mul (cop n)).1 ⟨h2, h3⟩
      rw [← six_pow] at h6
      exact h6

theorem OMA.solution : type_of% @OMA.S_oeis_a283754.main := by
  refine ⟨exists_d, ?_⟩
  intro d hd n hn
  have h := forward d hd n hn
  have hz : ((2 * a (n + 1) : ℕ) : ℤ) = ((a n + d n * 3 ^ n : ℕ) : ℤ) := by rw [h]
  push_cast at hz
  linarith
