import OMAStatements.S_oeis_a163617

namespace OMA.P163617

open OMA.S_oeis_a163617

lemma a_odd (k : ℕ) : a (2 * k + 1) = 2 * a k + 2 + (-1) ^ k := by
  rw [a]
  have h1 : (2 * k + 1) % 2 ≠ 0 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [if_neg h1, h2]

lemma a_even (k : ℕ) (hk : 0 < k) : a (2 * k) = 2 * a k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  show a (2 * j + 1 + 1) = 2 * a (j + 1)
  rw [a]
  have h1 : (2 * j + 1 + 1) % 2 = 0 := by omega
  have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  rw [if_pos h1, h2]

lemma g_even (k : ℕ) : ((2 * k) ^^^ ((2 * k) / 2)) = 2 * (k ^^^ (k / 2)) + k % 2 := by
  have h := Nat.div_add_mod ((2 * k) ^^^ ((2 * k) / 2)) 2
  rw [Nat.xor_div_two, Nat.xor_mod_two_eq] at h
  have e1 : 2 * k / 2 = k := by omega
  rw [e1] at h ⊢
  omega

lemma g_odd (k : ℕ) :
    ((2 * k + 1) ^^^ ((2 * k + 1) / 2)) + k % 2 = 2 * (k ^^^ (k / 2)) + 1 := by
  have h := Nat.div_add_mod ((2 * k + 1) ^^^ ((2 * k + 1) / 2)) 2
  rw [Nat.xor_div_two, Nat.xor_mod_two_eq] at h
  have e1 : (2 * k + 1) / 2 = k := by omega
  rw [e1] at h ⊢
  omega

lemma neg_one_pow_eq (k : ℕ) : (-1 : ℤ) ^ k = 1 - 2 * ((k % 2 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, Nat.even_iff.mp h]; norm_num
  · rw [h.neg_one_pow, Nat.odd_iff.mp h]; norm_num

end OMA.P163617

open OMA.S_oeis_a163617 OMA.P163617 in
theorem OMA.solution : type_of% @OMA.S_oeis_a163617.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a]
    · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · have hk : 0 < k := by omega
        have ihk := ih k (by omega)
        have hg := g_even k
        have hp := neg_one_pow_eq k
        have hp2 : (-1 : ℤ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
        rw [a_even k hk, hp2, hg]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        rw [hp] at ihk
        linarith
      · have ihk := ih k (by omega)
        have hg := g_odd k
        have hp := neg_one_pow_eq k
        have hp2 : (-1 : ℤ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
        have hg' : (((2 * k + 1) ^^^ ((2 * k + 1) / 2) : ℕ) : ℤ) + ((k % 2 : ℕ) : ℤ)
            = 2 * ((k ^^^ (k / 2) : ℕ) : ℤ) + 1 := by exact_mod_cast hg
        rw [a_odd k, hp2, hp]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        rw [hp] at ihk
        linarith
