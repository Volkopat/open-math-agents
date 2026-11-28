import OMAReductions.R_mo_144208_R1

-- Step mo-144208.R1.H1: hypothesis H1 of reduction mo-144208.R1
-- Credit: @futurum-dev

/-! The case `n = 2`: `(1 + 2^a)^b = 1 + 2^c`. Write `a = d + 1`. By induction
`(1 + 2^a)^b = 1 + b·2^a + t·2^(a+1)`; since `c > a`, `2^(a+1)` divides `b·2^a`, so `b = 2m`.
With `y = (1 + 2^a)^m = z + 1` we get `z(z + 2) = 2^c`, so `z` and `z + 2` are powers of two and
`z = 2`. Then `(1 + 2^a)^m = 3` forces `m = 1`, `a = 1`, and `1 + 2^c = 9` gives `c = 3`. -/

namespace OMA.Mo144208H1

/-- `(1 + 2^(d+1))^b = 1 + b * 2^(d+1) + t * 2^(d+2)` for some `t`. -/
theorem expand (d b : ℕ) : ∃ t, (1 + 2 ^ (d + 1)) ^ b = 1 + b * 2 ^ (d + 1) + t * 2 ^ (d + 2) := by
  induction b with
  | zero => exact ⟨0, by simp⟩
  | succ b ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨b * 2 ^ d + t * (1 + 2 ^ (d + 1)), ?_⟩
    rw [pow_succ, ht]
    have e1 : (2 : ℕ) ^ (d + 2) = 2 ^ (d + 1) * 2 := by rw [pow_succ]
    have e2 : (2 : ℕ) ^ (d + 1) = 2 ^ d * 2 := by rw [pow_succ]
    rw [e1, e2]; ring

/-- Two powers of two differing by two are `2` and `4`. -/
theorem two_pows {z c : ℕ} (hz : 2 ≤ z) (h : z * (z + 2) = 2 ^ c) : z = 2 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ h)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ h)
  rcases i with _ | _ | i
  · simp at hi; omega
  · simpa using hi
  · rcases j with _ | _ | j
    · simp at hj
    · simp at hj; omega
    · rw [pow_succ, pow_succ] at hi hj
      omega

theorem case_two (a b c : ℕ) (ha : 0 < a) (hb : 2 ≤ b) (_hc : 0 < c)
    (h : (1 + 2 ^ a) ^ b = 1 + 2 ^ c) : (a, b, c) = (1, 2, 3) := by
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  -- c > a
  have hca : d + 1 < c := by
    have h2 : (1 + 2 ^ (d + 1)) ^ 2 ≤ (1 + 2 ^ (d + 1)) ^ b :=
      Nat.pow_le_pow_right (by positivity) hb
    have hp : 0 < 2 ^ (d + 1) := by positivity
    have : 2 ^ (d + 1) < 2 ^ c := by nlinarith
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  -- b is even
  obtain ⟨t, ht⟩ := expand d b
  have hb2 : 2 ∣ b := by
    have h1 : 2 ^ (d + 2) ∣ 2 ^ c := pow_dvd_pow 2 (by omega)
    have h3 : 2 ^ c = b * 2 ^ (d + 1) + t * 2 ^ (d + 2) := by omega
    rw [h3] at h1
    have h4 : 2 ^ (d + 2) ∣ b * 2 ^ (d + 1) :=
      (Nat.dvd_add_left (Dvd.intro_left _ rfl)).1 h1
    rw [pow_succ, mul_comm b] at h4
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h4
  obtain ⟨m, rfl⟩ := hb2
  have hm : 1 ≤ m := by omega
  have hyy : (1 + 2 ^ (d + 1)) ^ m * (1 + 2 ^ (d + 1)) ^ m = 1 + 2 ^ c := by
    rw [← h, ← pow_add]; ring_nf
  have hbase : 3 ≤ 1 + 2 ^ (d + 1) := by
    have : 2 ≤ 2 ^ (d + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle : 1 + 2 ^ (d + 1) ≤ (1 + 2 ^ (d + 1)) ^ m := by
    calc 1 + 2 ^ (d + 1) = (1 + 2 ^ (d + 1)) ^ 1 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by positivity) hm
  generalize hy : (1 + 2 ^ (d + 1)) ^ m = y at hyy hle
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
  have hz : z * (z + 2) = 2 ^ c := by nlinarith
  have hz2 := two_pows (by omega) hz
  subst hz2
  -- m = 1 and a = 1
  have hm1 : m = 1 := by
    by_contra hne
    have : (1 + 2 ^ (d + 1)) ^ 2 ≤ (1 + 2 ^ (d + 1)) ^ m :=
      Nat.pow_le_pow_right (by positivity) (by omega)
    rw [hy] at this
    nlinarith
  subst hm1
  have hd : 2 ^ (d + 1) = 2 ^ 1 := by simp at hy; omega
  have hd0 : d = 0 := by
    have := Nat.pow_right_injective (le_refl 2) hd
    omega
  subst hd0
  have hc3 : 2 ^ c = 2 ^ 3 := by omega
  have := Nat.pow_right_injective (le_refl 2) hc3
  simp [this]

end OMA.Mo144208H1

theorem OMA.solution : OMA.R_mo_144208_R1.H1 := OMA.Mo144208H1.case_two
