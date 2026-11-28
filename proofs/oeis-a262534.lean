import OMAStatements.S_oeis_a262534

namespace OMA.A262534

/-- If `2 * phi(m) = m` with `m ≠ 0`, then `m` is a positive power of two. -/
lemma pow_two_of_totient {m : ℕ} (hm : m ≠ 0) (h : 2 * Nat.totient m = m) :
    ∃ a, 1 ≤ a ∧ m = 2 ^ a := by
  obtain ⟨v, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hcop : Nat.Coprime (2 ^ v) t :=
    Nat.Coprime.pow_left v (Nat.coprime_two_left.mpr ht)
  rw [Nat.totient_mul hcop] at h
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · exfalso
    simp only [pow_zero, Nat.totient_one, one_mul] at h
    have := Nat.totient_le t
    have h2 : t % 2 = 1 := Nat.odd_iff.mp ht
    omega
  · rw [Nat.totient_prime_pow Nat.prime_two hv] at h
    have hv' : 2 ^ v = 2 * 2 ^ (v - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : 0 < 2 ^ (v - 1) := by positivity
    have htt : Nat.totient t = t := by
      rw [hv'] at h
      have : 2 * 2 ^ (v - 1) * Nat.totient t = 2 * 2 ^ (v - 1) * t := by
        rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    have ht1 : t = 1 := by
      by_contra hne
      have := Nat.totient_lt t (by omega)
      omega
    exact ⟨v, hv, by rw [ht1, mul_one]⟩

/-- If `phi(2^a - 1) = 2^(a-1)`, then `a` divides `2^(a-1)`. -/
lemma dvd_of_totient {a : ℕ} (ha : 1 ≤ a) (h : Nat.totient (2 ^ a - 1) = 2 ^ (a - 1)) :
    a ∣ 2 ^ (a - 1) := by
  have hsplit : 2 ^ a = 2 * 2 ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
  have hcop : Nat.Coprime 2 (2 ^ a - 1) :=
    Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  have hmod := Nat.ModEq.pow_totient hcop
  have hdvd : 2 ^ a - 1 ∣ 2 ^ Nat.totient (2 ^ a - 1) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hmod.symm
  have hg : Nat.gcd (2 ^ a - 1) (2 ^ Nat.totient (2 ^ a - 1) - 1) = 2 ^ a - 1 :=
    Nat.gcd_eq_left hdvd
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  have h1 : 1 ≤ 2 ^ Nat.gcd a (Nat.totient (2 ^ a - 1)) := Nat.one_le_two_pow
  have h3 : 2 ^ Nat.gcd a (Nat.totient (2 ^ a - 1)) = 2 ^ a := by omega
  have h4 : Nat.gcd a (Nat.totient (2 ^ a - 1)) = a := Nat.pow_right_injective (le_refl 2) h3
  have hd := Nat.gcd_dvd_right a (Nat.totient (2 ^ a - 1))
  rw [h4, h] at hd
  exact hd

lemma tot_pow (a : ℕ) (ha : 0 < a) : Nat.totient (2 ^ a) = 2 ^ (a - 1) := by
  rw [Nat.totient_prime_pow Nat.prime_two ha]; simp

lemma mem_3 : OMA.S_oeis_a262534.InA262534 3 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> decide

lemma mem_5 : OMA.S_oeis_a262534.InA262534 5 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> decide

lemma mem_17 : OMA.S_oeis_a262534.InA262534 17 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (17 - 2 : ℕ) = 3 * 5 by norm_num, show (17 - 1 : ℕ) = 2 ^ 4 by norm_num,
      tot_pow 4 (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num)]
    norm_num
  · rw [show (17 - 1 : ℕ) = 2 ^ 4 by norm_num, tot_pow 4 (by norm_num)]
    norm_num

lemma mem_257 : OMA.S_oeis_a262534.InA262534 257 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (257 - 2 : ℕ) = 3 * (5 * 17) by norm_num, show (257 - 1 : ℕ) = 2 ^ 8 by norm_num,
      tot_pow 8 (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num)]
    norm_num
  · rw [show (257 - 1 : ℕ) = 2 ^ 8 by norm_num, tot_pow 8 (by norm_num)]
    norm_num

lemma mem_65537 : OMA.S_oeis_a262534.InA262534 65537 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (65537 - 2 : ℕ) = 3 * (5 * (17 * 257)) by norm_num,
      show (65537 - 1 : ℕ) = 2 ^ 16 by norm_num,
      tot_pow 16 (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_mul (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
    norm_num
  · rw [show (65537 - 1 : ℕ) = 2 ^ 16 by norm_num, tot_pow 16 (by norm_num)]
    norm_num

lemma mem_big : OMA.S_oeis_a262534.InA262534 4294967297 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (4294967297 - 2 : ℕ) = 3 * (5 * (17 * (257 * 65537))) by norm_num,
      show (4294967297 - 1 : ℕ) = 2 ^ 32 by norm_num,
      tot_pow 32 (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num)]
    norm_num
  · rw [show (4294967297 - 1 : ℕ) = 2 ^ 32 by norm_num, tot_pow 32 (by norm_num)]
    norm_num

end OMA.A262534

theorem OMA.solution : type_of% @OMA.S_oeis_a262534.main := by
  intro k
  constructor
  · rintro ⟨⟨hk3, h1, h2⟩, hkle⟩
    obtain ⟨a, ha, hka⟩ := OMA.A262534.pow_two_of_totient (by omega : k - 1 ≠ 0) h2
    have hk2 : k - 2 = 2 ^ a - 1 := by omega
    have htot : Nat.totient (2 ^ a - 1) = 2 ^ (a - 1) := by
      rw [← hk2, h1, hka, OMA.A262534.tot_pow a (by omega)]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (OMA.A262534.dvd_of_totient ha htot)
    have ha32 : a ≤ 32 := by
      have : 2 ^ a ≤ 2 ^ 32 := by omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    have hi5 : i ≤ 5 := by
      have : 2 ^ i ≤ 2 ^ 5 := by omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    have hk : k = 2 ^ a + 1 := by omega
    subst hi
    interval_cases i <;> simp_all
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨OMA.A262534.mem_3, by norm_num⟩
    · exact ⟨OMA.A262534.mem_5, by norm_num⟩
    · exact ⟨OMA.A262534.mem_17, by norm_num⟩
    · exact ⟨OMA.A262534.mem_257, by norm_num⟩
    · exact ⟨OMA.A262534.mem_65537, by norm_num⟩
    · exact ⟨OMA.A262534.mem_big, by norm_num⟩
