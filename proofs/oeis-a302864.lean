import OMAStatements.S_oeis_a302864
import Mathlib

namespace OMA.A302864Proof

open OMA.S_oeis_a302864

/-- The last decimal digit of `2 ^ n` is not `0`, since `5` does not divide `2 ^ n`. -/
theorem two_pow_mod_ten_ne_zero (n : ℕ) : 2 ^ n % 10 ≠ 0 := by
  intro h
  have h10 : 10 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h
  have h5 : 5 ∣ 2 ^ n := Nat.dvd_trans (by norm_num) h10
  have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h5
  norm_num at h52

/-- If `D` is a list of decimal digits whose first entry is nonzero, then the list
`D ++ (k zeros) ++ D.reverse` is the digit list of its own value. -/
theorem digits_pal (D T : List ℕ) (d k : ℕ) (hD : D = d :: T) (hd : d ≠ 0)
    (hlt : ∀ x ∈ D, x < 10) :
    Nat.digits 10 (Nat.ofDigits 10 (D ++ List.replicate k 0 ++ D.reverse)) =
      D ++ List.replicate k 0 ++ D.reverse := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro x hx
    simp only [List.mem_append, List.mem_reverse, List.mem_replicate] at hx
    rcases hx with (hx | ⟨-, rfl⟩) | hx
    · exact hlt x hx
    · norm_num
    · exact hlt x hx
  · subst hD
    have hW : d :: T ++ List.replicate k 0 ++ (d :: T).reverse =
        (d :: T ++ List.replicate k 0 ++ T.reverse) ++ [d] := by
      simp
    rw [hW]
    intro h
    rw [List.getLast_concat]
    exact hd

/-- The witness: with `D` the digit list of `2 ^ n` (first entry `d ≠ 0`), the number with digit list
`D ++ (n + 1 zeros) ++ D.reverse` is `Good n`. -/
theorem exists_good_aux (n : ℕ) (D T : List ℕ) (d : ℕ) (hD : D = d :: T) (hd : d ≠ 0)
    (hlt : ∀ x ∈ D, x < 10) (hof : Nat.ofDigits 10 D = 2 ^ n) : ∃ p, Good n p := by
  have hdig := digits_pal D T d (n + 1) hD hd hlt
  generalize hP : Nat.ofDigits 10 (D ++ List.replicate (n + 1) 0 ++ D.reverse) = P at hdig
  have hval : P = 2 ^ n + 10 ^ (D.length + (n + 1)) * Nat.ofDigits 10 D.reverse := by
    rw [← hP, Nat.ofDigits_append, Nat.ofDigits_append_replicate_zero, hof, List.length_append,
      List.length_replicate]
  have h2 : 2 ^ (n + 1) ∣ 10 ^ (D.length + (n + 1)) :=
    (pow_dvd_pow (2 : ℕ) (by omega : n + 1 ≤ D.length + (n + 1))).trans
      (pow_dvd_pow_of_dvd (by norm_num : (2 : ℕ) ∣ 10) _)
  refine ⟨P, ?_⟩
  unfold Good IsPal
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hval]
    exact Nat.lt_of_lt_of_le (Nat.two_pow_pos n) (Nat.le_add_right _ _)
  · rw [hdig]
    simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.append_assoc]
  · rw [hval]
    exact dvd_add dvd_rfl
      (((pow_dvd_pow (2 : ℕ) (by omega : n ≤ n + 1)).trans h2).mul_right _)
  · intro h
    rw [hval] at h
    have h3 : 2 ^ (n + 1) ∣ 2 ^ n := (Nat.dvd_add_left (h2.mul_right _)).mp h
    have h4 : n + 1 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h3
    omega

/-- For every `n` there is a positive palindrome with exactly `n` trailing binary zeros. -/
theorem exists_good (n : ℕ) : ∃ p, Good n p :=
  exists_good_aux n (Nat.digits 10 (2 ^ n)) (Nat.digits 10 (2 ^ n / 10)) (2 ^ n % 10)
    (Nat.digits_def' (by norm_num) (Nat.two_pow_pos n)) (two_pow_mod_ten_ne_zero n)
    (fun _ hx => Nat.digits_lt_base (by norm_num) hx) (Nat.ofDigits_digits 10 (2 ^ n))

/-- `Nat.find` gives a `Good` number, hence a positive one, whatever the decidability instance. -/
theorem find_pos' {n : ℕ} (h : ∃ p, Good n p) (inst : DecidablePred fun p => Good n p) :
    0 < @Nat.find _ inst h :=
  (@Nat.find_spec _ inst h).1

end OMA.A302864Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a302864.main := by
  intro n
  have h := OMA.A302864Proof.exists_good n
  unfold OMA.S_oeis_a302864.a
  rw [dif_pos h]
  exact OMA.A302864Proof.find_pos' h _
