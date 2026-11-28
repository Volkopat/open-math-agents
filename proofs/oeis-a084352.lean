import OMAStatements.S_oeis_a084352

namespace OMA.S_oeis_a084352

private theorem leading_digit_bound {m : ℕ} (hm : m ≠ 0)
    (h : ∀ x ∈ Nat.digits 10 m, 4 ≤ x) :
    4 * 10 ^ ((Nat.digits 10 m).length - 1) ≤ m := by
  let ds := Nat.digits 10 m
  have hne : ds ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  let d := ds.getLast hne
  have hd : 4 ≤ d := h d (List.getLast_mem hne)
  have hds : ds.dropLast ++ [d] = ds := List.dropLast_append_getLast hne
  have hlen : ds.dropLast.length = ds.length - 1 := List.length_dropLast
  change 4 * 10 ^ (ds.length - 1) ≤ m
  rw [← hlen]
  calc
    _ ≤ 10 ^ ds.dropLast.length * d := by
      rw [mul_comm 4]
      exact Nat.mul_le_mul_left _ hd
    _ ≤ Nat.ofDigits 10 (ds.dropLast ++ [d]) := by
      rw [Nat.ofDigits_append, Nat.ofDigits_singleton]
      exact Nat.le_add_left _ _
    _ = m := by rw [hds]; exact Nat.ofDigits_digits 10 m

private theorem even_product_length {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hlen : (Nat.digits 10 p).length = (Nat.digits 10 q).length)
    (hpd : ∀ x ∈ Nat.digits 10 p, 4 ≤ x) (hqd : ∀ x ∈ Nat.digits 10 q, 4 ≤ x) :
    Even (Nat.digits 10 (p * q)).length := by
  let k := (Nat.digits 10 p).length - 1
  have hlenp : (Nat.digits 10 p).length = k + 1 := by
    have hne : Nat.digits 10 p ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hp.ne'
    have hl := List.length_pos_iff.mpr hne
    dsimp [k]
    omega
  have hpLower : 4 * 10 ^ k ≤ p := leading_digit_bound hp.ne' hpd
  have hqLower : 4 * 10 ^ k ≤ q := by
    rw [show k = (Nat.digits 10 q).length - 1 from congrArg (· - 1) hlen]
    exact leading_digit_bound hq.ne' hqd
  have hpUpper : p < 10 ^ (k + 1) := by
    rw [← hlenp]
    exact Nat.lt_base_pow_length_digits (by decide)
  have hqUpper : q < 10 ^ (k + 1) := by
    rw [← hlenp, hlen]
    exact Nat.lt_base_pow_length_digits (by decide)
  have hlo : 10 ^ (k + k + 1) ≤ p * q := calc
    _ = 10 * 10 ^ k * 10 ^ k := by rw [pow_succ, pow_add]; ring
    _ ≤ (4 * 10 ^ k) * (4 * 10 ^ k) := by nlinarith [sq_nonneg (10 ^ k : ℤ)]
    _ ≤ _ := Nat.mul_le_mul hpLower hqLower
  have hhi : p * q < 10 ^ (k + k + 1 + 1) := calc
    _ < 10 ^ (k + 1) * q := Nat.mul_lt_mul_of_pos_right hpUpper hq
    _ ≤ 10 ^ (k + 1) * 10 ^ (k + 1) := Nat.mul_le_mul_left _ hqUpper.le
    _ = _ := by rw [← pow_add]; congr 1; omega
  refine ⟨k + 1, ?_⟩
  rw [Nat.length_digits 10 (p * q) (by decide) (mul_ne_zero hp.ne' hq.ne'),
    Nat.log_eq_of_pow_le_of_lt_pow hlo hhi]
  omega

private theorem prime_divisible_by_eleven_has_one {p : ℕ} (hp : p.Prime) (h : 11 ∣ p) :
    1 ∈ Nat.digits 10 p := by
  rcases (Nat.dvd_prime hp).mp h with h | h
  · omega
  · rw [← h]
    decide

end OMA.S_oeis_a084352

open OMA.S_oeis_a084352 in
theorem OMA.solution : type_of% @OMA.S_oeis_a084352.main := by
  intro p q hp hq hlen hpal
  by_contra h
  have hpd (d : ℕ) (hmem : d ∈ Nat.digits 10 p) : 4 ≤ d := by
    have hle : minDigit p q ≤ d := Nat.sInf_le (Or.inl hmem)
    omega
  have hqd (d : ℕ) (hmem : d ∈ Nat.digits 10 q) : 4 ≤ d := by
    have hle : minDigit p q ≤ d := Nat.sInf_le (Or.inr hmem)
    omega
  have he := even_product_length hp.pos hq.pos hlen hpd hqd
  have hdiv := Nat.eleven_dvd_of_palindrome (List.Palindrome.of_reverse_eq hpal) he
  rcases (show Nat.Prime 11 by decide).dvd_mul.mp hdiv with hdiv | hdiv
  · have := hpd 1 (prime_divisible_by_eleven_has_one hp hdiv)
    omega
  · have := hqd 1 (prime_divisible_by_eleven_has_one hq hdiv)
    omega
