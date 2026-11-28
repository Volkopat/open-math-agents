import OMAStatements.S_oeis_a208341
import Mathlib

open OMA.S_oeis_a208341

open Polynomial

private def F (a b : ℕ) : ℕ := ∑ i ∈ Finset.range (a + 1), (b + i).choose i * a.choose i

private lemma T_eq (n k : ℕ) (h : k ≤ n) : T n k = (F k (n - k) : ℚ) := by
  unfold T hyp2F1 F
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  simp at hj
  have e1 : (ascPochhammer ℚ j).eval ((n : ℚ) - k + 1) = (((n - k + 1).ascFactorial j : ℕ) : ℚ) := by
    rw [← ascPochhammer_nat_eq_ascFactorial, ascPochhammer_eval_cast]
    push_cast [Nat.cast_sub h]; ring_nf
  have e2 : (ascPochhammer ℚ j).eval (-(k : ℚ)) = (-1) ^ j * ((k.descFactorial j : ℕ) : ℚ) := by
    rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  have e3 : (ascPochhammer ℚ j).eval (1 : ℚ) = (j.factorial : ℚ) := by
    have := ascPochhammer_eval_cast ℚ j 1
    rw [ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial] at this
    push_cast at this; rw [← this]
  rw [e1, e2, e3, Nat.ascFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have hf : (j.factorial : ℚ) ≠ 0 := by positivity
  have hs : ((-1 : ℚ) ^ j) * ((-1) ^ j) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  push_cast
  field_simp
  linear_combination (((n - k + j).choose j : ℕ) : ℚ) * ((k.choose j : ℕ) : ℚ) * hs

private lemma vand (b i : ℕ) : (b + i).choose i = ∑ j ∈ Finset.range (i + 1), b.choose j * i.choose j := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j hj
  simp at hj
  rw [Nat.choose_symm (by omega)]

private lemma sumc (a j : ℕ) : ∑ i ∈ Finset.range (a + 1), a.choose i * i.choose j = a.choose j * 2 ^ (a - j) := by
  rcases Nat.lt_or_ge a j with h | h
  · rw [Nat.choose_eq_zero_of_lt h, zero_mul]
    apply Finset.sum_eq_zero; intro i hi; simp at hi
    rw [Nat.choose_eq_zero_of_lt (show i < j by omega), mul_zero]
  · obtain ⟨r, rfl⟩ : ∃ r, a = j + r := ⟨a - j, by omega⟩
    rw [show j + r + 1 = j + (r + 1) by ring, Finset.sum_range_add,
      Finset.sum_eq_zero (fun i hi => by simp at hi; rw [Nat.choose_eq_zero_of_lt (show i < j by omega), mul_zero]),
      zero_add, show j + r - j = r by omega, ← Nat.sum_range_choose r, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    simp at ht
    rw [@Nat.choose_mul (j + r) (j + t) j (by omega), show j + r - j = r by omega, show j + t - j = t by omega]

private lemma FG (a b : ℕ) : F a b = ∑ i ∈ Finset.range (a + 1), 2 ^ (a - i) * b.choose i * a.choose i := by
  unfold F
  have h1 : ∀ i ∈ Finset.range (a + 1), (b + i).choose i * a.choose i =
      ∑ j ∈ Finset.range (a + 1), a.choose i * (b.choose j * i.choose j) := by
    intro i hi
    simp at hi
    rw [vand, Finset.sum_mul]
    rw [show a + 1 = (i + 1) + (a - i) by omega, Finset.sum_range_add _ (i + 1) (a - i)]
    rw [Finset.sum_eq_zero (s := Finset.range (a - i)) (fun j _ => by
      rw [Nat.choose_eq_zero_of_lt (show i < i + 1 + j by omega)]; ring), add_zero]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp at hj
  have := sumc a j
  calc ∑ i ∈ Finset.range (a + 1), a.choose i * (b.choose j * i.choose j)
      = b.choose j * ∑ i ∈ Finset.range (a + 1), a.choose i * i.choose j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ = 2 ^ (a - j) * b.choose j * a.choose j := by rw [this]; ring

private lemma sym (a b : ℕ) : (F a b : ℚ) * 2 ^ b = (F b a : ℚ) * 2 ^ a := by
  rw [FG, FG]
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  have ext : ∀ (x y : ℕ), ∑ i ∈ Finset.range (x + 1), (2 : ℚ) ^ (x - i) * (y.choose i : ℚ) * (x.choose i : ℚ) * 2 ^ y =
      ∑ i ∈ Finset.range (x + y + 1), (2 : ℚ) ^ (x + y) / 2 ^ i * (y.choose i : ℚ) * (x.choose i : ℚ) := by
    intro x y
    rw [show x + y + 1 = (x + 1) + y by ring, Finset.sum_range_add _ (x + 1) y]
    rw [Finset.sum_eq_zero (s := Finset.range y) (fun i _ => by
      rw [Nat.choose_eq_zero_of_lt (show x < x + 1 + i by omega)]; simp), add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    simp at hi
    have : (2 : ℚ) ^ (x - i) = 2 ^ x / 2 ^ i := by
      rw [eq_div_iff (by positivity), ← pow_add, show x - i + i = x by omega]
    rw [this, pow_add]
    ring
  rw [ext, ext, add_comm b a]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a208341.main := by
  intro n k h
  rw [T_eq n k h, T_eq n (n - k) (by omega), show n - (n - k) = k by omega]
  have hs := sym k (n - k)
  have h2 : (2 : ℚ) ^ ((n : ℤ) - 2 * k) * 2 ^ k = 2 ^ (n - k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    push_cast [Nat.cast_sub h]; ring
  have h3 : (2 : ℚ) ^ k ≠ 0 := by positivity
  apply mul_right_cancel₀ h3
  rw [mul_assoc, h2, hs]
