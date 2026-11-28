import OMAStatements.S_oeis_a110408

namespace OMA.S_oeis_a110408




theorem rev_143 : rev 143 = 341 := by
  norm_num [rev, Nat.ofDigits]

theorem digits_341 : Nat.digits 10 341 = [1, 4, 3] := by
  norm_num

theorem digits_143 : Nat.digits 10 143 = [3, 4, 1] := by
  norm_num

/-- Every block rev(143) = 341 is a multiple of 11, so is any number of copies of it. -/
theorem dvd_blocks (m : ℕ) : 11 ∣ Nat.ofDigits 10 (List.replicate m [1, 4, 3]).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append]
    have h341 : Nat.ofDigits 10 [1, 4, 3] = 341 := by norm_num [Nat.ofDigits]
    rw [h341]
    exact dvd_add (by norm_num) (dvd_mul_of_dvd_right ih _)

theorem F_143 (m : ℕ) :
    F 143 m = 143 + 1000 * Nat.ofDigits 10 (List.replicate m [1, 4, 3]).flatten := by
  unfold F
  rw [rev_143, digits_341, digits_143, Nat.ofDigits_append]
  norm_num [Nat.ofDigits]

/-- a(143) = 0. -/
theorem zero_143 : ZeroTerm 143 := by
  intro m _ hp
  have h11 : 11 ∣ F 143 m := by
    rw [F_143]
    exact dvd_add (by norm_num) (dvd_mul_of_dvd_right (dvd_blocks m) _)
  have hge : 143 ≤ F 143 m := by
    rw [F_143]
    omega
  rcases hp.eq_one_or_self_of_dvd 11 h11 with h | h <;> omega

/-- 143 = 11 * 13 is not a prime (in particular not a palindromic prime) and not a multiple of 3. -/
theorem not_pal_prime_143 : ¬ ((Nat.Prime 143 ∧ rev 143 = 143) ∨ 143 % 3 = 0) := by
  rintro (⟨hp, -⟩ | h)
  · exact absurd hp (by norm_num)
  · omega

/-- Murthy's characterization of the zero terms is false. -/
theorem disproof : ¬ ∀ n : ℕ, (n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9) →
    (ZeroTerm n ↔ ((n.Prime ∧ rev n = n) ∨ n % 3 = 0)) := by
  intro h
  exact not_pal_prime_143 ((h 143 (by norm_num)).mp zero_143)

end OMA.S_oeis_a110408

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a110408.main) :=
  OMA.S_oeis_a110408.disproof
