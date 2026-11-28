import OMAStatements.S_oeis_a088884

open OMA.S_oeis_a088884

lemma concatRev_mod3 (p : ℕ) : concatRev p ≡ 2 * p [MOD 3] := by
  unfold concatRev
  have h1 : p ≡ (Nat.digits 10 p).sum [MOD 3] := Nat.modEq_three_digits_sum p
  have h2 : Nat.ofDigits 10 (Nat.digits 10 p).reverse ≡ (Nat.digits 10 p).sum [MOD 3] := by
    have := Nat.ofDigits_modEq 10 3 (Nat.digits 10 p).reverse
    simpa [Nat.ofDigits_one, List.sum_reverse] using this
  have h3 : 10 ^ (Nat.digits 10 p).length ≡ 1 [MOD 3] := by
    have := Nat.ModEq.pow (Nat.digits 10 p).length (show 10 ≡ 1 [MOD 3] by decide)
    simpa using this
  have h4 : p * 10 ^ (Nat.digits 10 p).length ≡ p * 1 [MOD 3] := Nat.ModEq.mul_left p h3
  have h5 := Nat.ModEq.add h4 (h2.trans h1.symm)
  rw [mul_one] at h5
  rw [two_mul]
  exact h5

lemma concatRev_ge (p : ℕ) (hp : 2 ≤ p) : 20 ≤ concatRev p := by
  unfold concatRev
  have hL : 1 ≤ (Nat.digits 10 p).length := by
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp
  have : 10 ≤ 10 ^ (Nat.digits 10 p).length := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hL
  have := Nat.mul_le_mul hp this
  omega

lemma not_prime_of_three (n : ℕ) (h3 : 3 ∣ n) (hn : 3 < n) : ¬ n.Prime := by
  intro hp
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
  omega

lemma concatRev_two : concatRev 2 = 22 := by
  norm_num [concatRev]

lemma concatRev_three : concatRev 3 = 33 := by
  norm_num [concatRev]

theorem OMA.solution : type_of% @OMA.S_oeis_a088884.main := by
  refine ⟨?_, ?_⟩
  · intro p hp hq h3
    have hm := concatRev_mod3 p
    have hge := concatRev_ge p hp.two_le
    unfold Nat.ModEq at hm
    have hp3 : p % 3 ≠ 0 := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    have hp1 : p % 3 ≠ 1 := by
      intro h
      exact not_prime_of_three _ (by omega) (by omega) hq
    rcases hp.eq_two_or_odd with h2 | h2
    · subst h2
      rw [concatRev_two] at hq
      norm_num at hq
    · omega
  · intro p hp
    have hm := concatRev_mod3 p
    have hge := concatRev_ge p hp.two_le
    unfold Nat.ModEq at hm
    by_cases hp3 : p = 3
    · subst hp3
      rw [concatRev_three]
      norm_num
    have hp0 : p % 3 ≠ 0 := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    have key : ¬ (concatRev p - 2).Prime ∨ ¬ (concatRev p + 2).Prime := by
      rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h
      · exact Or.inl (not_prime_of_three _ (by omega) (by omega))
      · exact Or.inr (not_prime_of_three _ (by omega) (by omega))
    tauto
