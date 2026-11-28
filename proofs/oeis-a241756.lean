import OMAStatements.S_oeis_a241756
import Mathlib

open OMA.S_oeis_a241756

private def A (k : ℕ) : ℚ := gbinom (-1 / 4) k ^ 2

private lemma gb_succ (k : ℕ) : gbinom (-1 / 4) (k + 1) = gbinom (-1 / 4) k * (-(4 * k + 1) / (4 * (k + 1))) := by
  unfold gbinom
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

private lemma A_succ (k : ℕ) : A (k + 1) = A k * ((4 * k + 1) ^ 2 / (16 * (k + 1) ^ 2)) := by
  unfold A; rw [gb_succ]; field_simp; ring

private lemma A_zero : A 0 = 1 := by simp [A, gbinom]

private def G (n : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => ((k : ℚ) + 1) ^ 2 * (1 + k + 3 * ((n - k : ℕ) : ℚ)) / 3 * A (k + 1) * A (n - k)

private lemma step (n m : ℕ) (hm : m ≤ n) :
    (2 * (n : ℚ) + 1) ^ 3 * (A m * A (n - m)) - 8 * ((n : ℚ) + 1) ^ 3 * (A m * A (n + 1 - m)) =
      24 * (G n (m + 1) - G n m) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
  rcases m with _ | k
  · simp only [G, Nat.sub_zero, Nat.zero_add, zero_add]
    rw [show (1 : ℕ) = 0 + 1 from rfl, A_succ 0, A_succ j, A_zero]
    push_cast
    have h4 : ((j : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · simp only [G]
    rw [show k + 1 + j - (k + 1) = j by omega, show k + 1 + j - k = j + 1 by omega,
      show k + 1 + j + 1 - (k + 1) = j + 1 by omega, A_succ (k + 1), A_succ j]
    push_cast
    have h4 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have h5 : ((k : ℚ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

private lemma rec (n : ℕ) : 8 * ((n : ℚ) + 1) ^ 3 * grosjean (n + 1) = (2 * (n : ℚ) + 1) ^ 3 * grosjean n := by
  have htel : ∑ m ∈ Finset.range (n + 1), (G n (m + 1) - G n m) = G n (n + 1) - G n 0 :=
    Finset.sum_range_sub (G n) (n + 1)
  have hsum : ∑ m ∈ Finset.range (n + 1),
      ((2 * (n : ℚ) + 1) ^ 3 * (A m * A (n - m)) - 8 * ((n : ℚ) + 1) ^ 3 * (A m * A (n + 1 - m))) =
      24 * (G n (n + 1) - G n 0) := by
    rw [← htel, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m hm => step n m (by simp at hm; omega))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hG0 : G n 0 = 0 := by simp [G]
  have hG1 : G n (n + 1) = 8 * ((n : ℚ) + 1) ^ 3 * A (n + 1) / 24 := by
    simp only [G, Nat.sub_self, A_zero]
    push_cast
    ring
  have e1 : grosjean n = ∑ m ∈ Finset.range (n + 1), A m * A (n - m) := by
    unfold grosjean A; rfl
  have e2 : grosjean (n + 1) = ∑ m ∈ Finset.range (n + 1), A m * A (n + 1 - m) + A (n + 1) := by
    unfold grosjean
    rw [Finset.sum_range_succ, Nat.sub_self]
    unfold A
    simp [gbinom]
  rw [e1, e2]
  rw [hG0, hG1] at hsum
  linarith

private lemma closed (n : ℕ) : grosjean n = (Nat.centralBinom n : ℚ) ^ 3 / 64 ^ n := by
  induction n with
  | zero => simp [grosjean, gbinom]
  | succ n ih =>
    have h := rec n
    have hc : ((n + 1 : ℕ) : ℚ) * (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * Nat.centralBinom n := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    rw [ih] at h
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast at hc
    have : (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * Nat.centralBinom n / (n + 1) := by
      field_simp; linarith
    rw [this]
    field_simp at h ⊢
    rw [pow_succ]
    linear_combination 8 * h

private def ds (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma ds_pos (n : ℕ) (hn : 0 < n) : ds n = n % 2 + ds (n / 2) := by
  unfold ds; rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]

private lemma ds_two (n : ℕ) : ds (2 * n) = ds n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · rw [ds_pos _ (by omega), Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num), zero_add]

private lemma e_ds (n : ℕ) : A005187 n + ds n = 2 * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | k
    · simp [A005187, ds]
    · have h := ih ((k + 1) / 2) (by omega)
      rw [A005187, ds_pos _ (by omega)]
      omega

private lemma v2 (n : ℕ) : padicValNat 2 (Nat.centralBinom n) = ds n := by
  have hf : Nat.centralBinom n * n.factorial * n.factorial = (2 * n).factorial := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rwa [show 2 * n - n = n by omega] at this
  have h1 := sub_one_mul_padicValNat_factorial (p := 2) (2 * n)
  have h2 := sub_one_mul_padicValNat_factorial (p := 2) n
  have c0 := Nat.centralBinom_ne_zero n
  have f0 := Nat.factorial_ne_zero n
  rw [← hf, padicValNat.mul (mul_ne_zero c0 f0) f0, padicValNat.mul c0 f0] at h1
  have hle : ds n ≤ n := Nat.digit_sum_le 2 n
  change (2 - 1) * _ = 2 * n - ds (2 * n) at h1
  change (2 - 1) * _ = n - ds n at h2
  rw [ds_two] at h1
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a241756.main := by
  intro n
  unfold a
  obtain ⟨k, u, hu, hC⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.centralBinom_ne_zero n)
  have hk : k = ds n := by
    rw [← v2, hC, padicValNat.mul (by positivity) (by rintro rfl; simp at hu),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by
        rintro h; exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h))]
    simp
  have he := e_ds n
  have hle : ds n ≤ n := Nat.digit_sum_le 2 n
  have hg : grosjean n = ((u ^ 3 : ℕ) : ℤ) / ((2 ^ (3 * A005187 n) : ℕ) : ℤ) := by
    rw [closed, hC]
    push_cast
    rw [show (64 : ℚ) ^ n = 2 ^ (3 * A005187 n) * (2 ^ k) ^ 3 by
      rw [← pow_mul, ← pow_add, show (64 : ℚ) = 2 ^ 6 by norm_num, ← pow_mul]
      congr 1; omega]
    have : (2 : ℚ) ^ k ≠ 0 := by positivity
    field_simp
  rw [hg]
  have hcop : Nat.Coprime (u ^ 3) (2 ^ (3 * A005187 n)) :=
    Nat.Coprime.pow _ _ (Nat.coprime_two_right.mpr hu)
  have := Rat.den_div_eq_of_coprime (a := ((u ^ 3 : ℕ) : ℤ)) (b := ((2 ^ (3 * A005187 n) : ℕ) : ℤ))
    (by positivity) (by simpa using hcop)
  rw [pow_mul] at this ⊢
  norm_num at this ⊢
  exact_mod_cast this
