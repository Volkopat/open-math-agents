import OMAStatements.S_oeis_a267598

namespace OMA.S_oeis_a267598

lemma ruleOut177 (l c r : Bool) : ruleOut 177 l c r = ((!c && !r) || (l && r)) := by
  cases l <;> cases c <;> cases r <;> decide

/-- Closed form of Rule 177 from step 1 on. -/
lemma cell_eq (t : ℕ) (ht : 1 ≤ t) (i : ℤ) :
    cell 177 t i = decide (i < -(t : ℤ) ∨ (t : ℤ) ≤ i ∨ (i ≠ (t : ℤ) - 1 ∧ (i + t) % 2 = 1)) := by
  induction t, ht using Nat.le_induction generalizing i with
  | base =>
    simp only [cell, ruleOut177]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]
    push_cast
    omega
  | succ t ht ih =>
    simp only [cell, ruleOut177, ih]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]
    push_cast
    omega

theorem solution : ∀ n : ℕ, a n = (1 - (-1 : ℤ) ^ (n + Nat.sqrt (n + 2))) / 2 := by
  intro n
  set r := Nat.sqrt n with hr
  set s := Nat.sqrt (n + 2) with hs
  have h1 : r * r ≤ n := Nat.sqrt_le n
  have h2 : n < (r + 1) * (r + 1) := Nat.lt_succ_sqrt n
  have h3 : r ≤ s := Nat.sqrt_le_sqrt (by omega)
  have h4 : s < r + 2 := by
    rw [hs, Nat.sqrt_lt']
    nlinarith
  have h5 : s = r + 1 ↔ (r + 1) * (r + 1) ≤ n + 2 := by
    constructor
    · intro h; rw [← h]; exact Nat.sqrt_le (n + 2)
    · intro h
      have : r + 1 ≤ s := Nat.le_sqrt.mpr h
      omega
  have hpar : (r * r + r) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self r)
  have key : (if cell 177 r (((n - r * r : ℕ) : ℤ) - (r : ℤ)) then (1 : ℤ) else 0) =
      if (n + s) % 2 = 1 then 1 else 0 := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · have hn : n = 0 := by rw [h0] at h2; omega
      have hs0 : s = 1 := by
        rw [hs, hn]
        refine le_antisymm ?_ (Nat.le_sqrt.mpr (by norm_num))
        exact Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by norm_num))
      rw [h0, hn, hs0]
      decide
    · rw [cell_eq r h0]
      have e : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
      rw [e] at h2 h5
      generalize r * r = R at *
      by_cases hc : (n + s) % 2 = 1
      · rw [if_pos hc, if_pos]
        simp only [decide_eq_true_eq]
        omega
      · rw [if_neg hc, if_neg]
        simp only [decide_eq_true_eq]
        omega
  show (if cell 177 r (((n - r * r : ℕ) : ℤ) - (r : ℤ)) then 1 else 0) = _
  rw [key]
  rcases Nat.even_or_odd (n + s) with h | h
  · rw [h.neg_one_pow, if_neg (by rw [Nat.even_iff] at h; omega)]
    norm_num
  · rw [h.neg_one_pow, if_pos (Nat.odd_iff.mp h)]
    norm_num

end OMA.S_oeis_a267598

theorem OMA.solution : type_of% @OMA.S_oeis_a267598.main := OMA.S_oeis_a267598.solution
