import OMAStatements.S_oeis_a255683
import Mathlib

/-!
# A255683: a(2^n + i) = (2^(n+1) - 1) * A063787(i + 1)

Let l be a digit list of length L and v(r) the base-2 value of `l.rotate r`. If
`l.rotate r = d :: t` then `l.rotate (r + 1) = t ++ [d]`, so 2 v(r+1) + d = v(r) + d 2^L, where
d is the digit of l at position r. Summing over r < L, and using v(L) = v(0), gives
S + T = T 2^L, where S is the sum of the v(r) and T the digit sum of l. Hence
a(m) = T (2^L - 1), with T the number of 1 bits of m and L its number of bits.

For m = 2^n + i with i < 2^n: L = n + 1 and T = 1 + T(i). Finally A063787(i + 1) = 1 + T(i), by
strong induction from its defining rule (with T(2^k - 1) = k).
-/

namespace OMA.P255683

open OMA.S_oeis_a255683

/-- The digit sum of a list, as a sum over positions. -/
lemma sum_getD (l : List ℕ) : ∑ r ∈ Finset.range l.length, l.getD r 0 = l.sum := by
  induction l with
  | nil => simp
  | cons d t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
    rw [ih]
    ring

/-- One rotation step: 2 v(r+1) + l[r] = v(r) + l[r] 2^L. -/
lemma rot_step (l : List ℕ) (r : ℕ) (hr : r < l.length) :
    2 * Nat.ofDigits 2 (l.rotate (r + 1)) + l.getD r 0 =
      Nat.ofDigits 2 (l.rotate r) + l.getD r 0 * 2 ^ l.length := by
  have hlen : (l.rotate r).length = l.length := List.length_rotate l r
  have h0 : 0 < (l.rotate r).length := by omega
  have hd : l.getD r 0 = (l.rotate r).getD 0 0 := by
    rw [List.getD_eq_getElem _ _ hr, List.getD_eq_getElem _ _ h0, List.getElem_rotate]
    congr 1
    rw [Nat.zero_add, Nat.mod_eq_of_lt hr]
  rw [hd, ← List.rotate_rotate, ← hlen]
  generalize l.rotate r = m at *
  cases m with
  | nil => simp at h0
  | cons d t =>
    simp only [List.rotate_cons_succ, List.rotate_zero, List.getD_cons_zero, Nat.ofDigits_append,
      Nat.ofDigits_cons, Nat.ofDigits_nil, List.length_cons, pow_succ]
    ring

/-- The sum of the values of the L rotations of a digit list is (digit sum) * (2^L - 1). -/
lemma rot_sum (l : List ℕ) :
    ∑ r ∈ Finset.range l.length, Nat.ofDigits 2 (l.rotate r) = l.sum * (2 ^ l.length - 1) := by
  have hshift : ∑ r ∈ Finset.range l.length, Nat.ofDigits 2 (l.rotate (r + 1)) =
      ∑ r ∈ Finset.range l.length, Nat.ofDigits 2 (l.rotate r) := by
    have h1 := Finset.sum_range_succ' (fun r => Nat.ofDigits 2 (l.rotate r)) l.length
    have h2 := Finset.sum_range_succ (fun r => Nat.ofDigits 2 (l.rotate r)) l.length
    simp only [List.rotate_length, List.rotate_zero] at h1 h2
    omega
  have hstep : ∑ r ∈ Finset.range l.length, (2 * Nat.ofDigits 2 (l.rotate (r + 1)) + l.getD r 0) =
      ∑ r ∈ Finset.range l.length, (Nat.ofDigits 2 (l.rotate r) + l.getD r 0 * 2 ^ l.length) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    exact rot_step l r hr
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hshift,
    sum_getD] at hstep
  rw [Nat.mul_sub_one]
  generalize ∑ r ∈ Finset.range l.length, Nat.ofDigits 2 (l.rotate r) = S at *
  generalize l.sum * 2 ^ l.length = X at *
  omega

/-- The binary digit sum of i is i % 2 plus the digit sum of i / 2. -/
lemma digits_sum_step (i : ℕ) : (Nat.digits 2 i).sum = i % 2 + (Nat.digits 2 (i / 2)).sum := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simp
  · rw [Nat.digits_def' (by norm_num) h, List.sum_cons]

/-- Adding 2^n to i < 2^n adds one 1 bit. -/
lemma digits_sum_pow_add (n i : ℕ) (hi : i < 2 ^ n) :
    (Nat.digits 2 (2 ^ n + i)).sum = 1 + (Nat.digits 2 i).sum := by
  induction n generalizing i with
  | zero =>
    have : i = 0 := by simpa using hi
    subst this
    simp
  | succ n ih =>
    rw [digits_sum_step (2 ^ (n + 1) + i), digits_sum_step i]
    have h1 : (2 ^ (n + 1) + i) % 2 = i % 2 := by rw [pow_succ]; omega
    have h2 : (2 ^ (n + 1) + i) / 2 = 2 ^ n + i / 2 := by rw [pow_succ]; omega
    rw [h1, h2, ih (i / 2) (by rw [pow_succ] at hi; omega)]
    ring

/-- 2^n + i, with i < 2^n, has n + 1 binary digits. -/
lemma digits_len_pow_add (n i : ℕ) (hi : i < 2 ^ n) :
    (Nat.digits 2 (2 ^ n + i)).length = n + 1 := by
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hlog : Nat.log 2 (2 ^ n + i) = n :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
  rw [Nat.length_digits 2 _ (by norm_num) (by omega), hlog]

/-- 2^k - 1 has k one bits. -/
lemma digits_sum_pow_sub_one (k : ℕ) : (Nat.digits 2 (2 ^ k - 1)).sum = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [digits_sum_step]
    have h1 : (2 ^ (k + 1) - 1) % 2 = 1 := by rw [pow_succ]; omega
    have h2 : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by rw [pow_succ]; omega
    rw [h1, h2, ih]
    ring

/-- A063787(i + 1) = 1 + (number of 1 bits of i). -/
lemma b_eq (i : ℕ) : b (i + 1) = 1 + (Nat.digits 2 i).sum := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [b.eq_1]
    have hne : i + 1 ≠ 0 := by omega
    rw [dif_neg hne]
    have hlo : 2 ^ Nat.log 2 (i + 1) ≤ i + 1 := Nat.pow_log_le_self 2 hne
    have hhi : i + 1 < 2 ^ (Nat.log 2 (i + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) (i + 1)
    have hpos : 1 ≤ 2 ^ Nat.log 2 (i + 1) := Nat.one_le_two_pow
    generalize Nat.log 2 (i + 1) = k at *
    split_ifs with heq
    · have hi : i = 2 ^ k - 1 := by omega
      rw [hi, digits_sum_pow_sub_one]
      ring
    · obtain ⟨j, hj⟩ : ∃ j, i + 1 - 2 ^ k = j + 1 := ⟨i - 2 ^ k, by omega⟩
      rw [pow_succ] at hhi
      rw [hj, ih j (by omega)]
      have hi : i = 2 ^ k + j := by omega
      rw [hi, digits_sum_pow_add k j (by omega)]

theorem sol : type_of% @OMA.S_oeis_a255683.main := by
  intro n i hi
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hi' : i < 2 ^ n := by omega
  unfold a
  rw [rot_sum, digits_len_pow_add n i hi', digits_sum_pow_add n i hi', b_eq, Nat.mul_comm]

end OMA.P255683

theorem OMA.solution : type_of% @OMA.S_oeis_a255683.main := OMA.P255683.sol

