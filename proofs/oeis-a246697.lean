import OMAStatements.S_oeis_a246697

namespace OMA.P246697

open OMA.S_oeis_a246697 Finset

lemma row_zero (x0 x1 : ℤ) : row x0 x1 0 = x0 := by rw [row]

lemma row_one (x0 x1 : ℤ) : row x0 x1 1 = x1 := by rw [row]

lemma row_add_two (x0 x1 : ℤ) (k : ℕ) : row x0 x1 (k + 2) = row x0 x1 k + 2 := by rw [row]

lemma row_even (x0 x1 : ℤ) (k j : ℕ) (h : k = 2 * j) : row x0 x1 k = x0 + 2 * (j : ℤ) := by
  subst h
  induction j with
  | zero =>
    show row x0 x1 0 = _
    rw [row_zero]
    simp
  | succ j ih =>
    have e : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [e, row_add_two, ih]
    push_cast
    ring

lemma row_odd (x0 x1 : ℤ) (k j : ℕ) (h : k = 2 * j + 1) : row x0 x1 k = x1 + 2 * (j : ℤ) := by
  subst h
  induction j with
  | zero =>
    show row x0 x1 1 = _
    rw [row_one]
    simp
  | succ j ih =>
    have e : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by ring
    rw [e, row_add_two, ih]
    push_cast
    ring

lemma row_congr {x0 x1 y0 y1 : ℤ} (h0 : x0 = y0) (h1 : x1 = y1) : row x0 x1 = row y0 y1 := by
  subst h0 h1
  rfl

lemma t_step (N P n : ℕ) (hP : P = n + 1) (hN : N = n + 2) :
    t N = row (if N % 2 = 1 then t P n + 2 else t P P + 2)
      (if N % 2 = 1 then t P P + 2 else t P n + 2) := by
  subst hP hN
  rw [t]

lemma base : t 2 = row 5 4 := by
  have h1 : t 1 1 = 3 := by decide
  have h0 : t 1 0 = 2 := by decide
  rw [t_step 2 1 0 rfl rfl, if_neg (by decide), if_neg (by decide), h1, h0]
  exact row_congr (by norm_num) (by norm_num)

lemma odd_from_even (m : ℕ) (X0 X1 : ℤ) (h : t (2 * m + 2) = row X0 X1) :
    t (2 * m + 3) = row (X1 + 2 * (m : ℤ) + 2) (X0 + 2 * (m : ℤ) + 4) := by
  have hc : (2 * m + 3) % 2 = 1 := by omega
  rw [t_step (2 * m + 3) (2 * m + 2) (2 * m + 1) (by omega) (by omega), if_pos hc, if_pos hc, h,
    row_odd X0 X1 (2 * m + 1) m (by omega), row_even X0 X1 (2 * m + 2) (m + 1) (by omega)]
  exact row_congr rfl (by push_cast; ring)

lemma even_from_odd (m : ℕ) (X0 X1 : ℤ) (h : t (2 * m + 3) = row X0 X1) :
    t (2 * m + 4) = row (X1 + 2 * (m : ℤ) + 4) (X0 + 2 * (m : ℤ) + 4) := by
  have hc : ¬ (2 * m + 4) % 2 = 1 := by omega
  rw [t_step (2 * m + 4) (2 * m + 3) (2 * m + 2) (by omega) (by omega), if_neg hc, if_neg hc, h,
    row_odd X0 X1 (2 * m + 3) (m + 1) (by omega), row_even X0 X1 (2 * m + 2) (m + 1) (by omega)]
  exact row_congr (by push_cast; ring) (by push_cast; ring)

lemma rows_even (m : ℕ) :
    t (2 * m + 2) = row (2 * (m : ℤ) ^ 2 + 6 * (m : ℤ) + 5) (2 * (m : ℤ) ^ 2 + 4 * (m : ℤ) + 4) := by
  induction m with
  | zero =>
    show t 2 = _
    rw [base]
    exact row_congr (by norm_num) (by norm_num)
  | succ m ih =>
    have ho := odd_from_even m _ _ ih
    have he := even_from_odd m _ _ ho
    have e : 2 * (m + 1) + 2 = 2 * m + 4 := by ring
    rw [e, he]
    exact row_congr (by push_cast; ring) (by push_cast; ring)

lemma rows_odd (m : ℕ) :
    t (2 * m + 3) = row (2 * (m : ℤ) ^ 2 + 6 * (m : ℤ) + 6) (2 * (m : ℤ) ^ 2 + 8 * (m : ℤ) + 9) := by
  rw [odd_from_even m _ _ (rows_even m)]
  exact row_congr (by ring) (by ring)

lemma sum_row (x0 x1 : ℤ) (j : ℕ) :
    ∑ k ∈ range (2 * j), row x0 x1 k = (j : ℤ) * (x0 + x1) + 2 * (j : ℤ) * ((j : ℤ) - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e, sum_range_succ, sum_range_succ, ih, row_even x0 x1 (2 * j) j rfl,
      row_odd x0 x1 (2 * j + 1) j rfl]
    push_cast
    ring

lemma a_even (m : ℕ) :
    a (2 * m + 2) = 4 * ((m : ℤ) + 1) ^ 3 + 6 * ((m : ℤ) + 1) ^ 2 + 5 * ((m : ℤ) + 1) + 1 := by
  unfold a
  have e : 2 * m + 2 + 1 = 2 * (m + 1) + 1 := by ring
  rw [rows_even m, e, sum_range_succ, sum_row, row_even _ _ (2 * (m + 1)) (m + 1) rfl]
  push_cast
  ring

lemma a_odd (m : ℕ) :
    a (2 * m + 3) = ((m : ℤ) + 2) * (4 * ((m : ℤ) + 1) ^ 2 + 8 * ((m : ℤ) + 1) + 5) := by
  unfold a
  have e : 2 * m + 3 + 1 = 2 * (m + 2) := by ring
  rw [rows_odd m, e, sum_row]
  push_cast
  ring

lemma closed_even (n m : ℕ) (h : n = 2 * m + 2) :
    4 * a n = 2 * (n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 9 * (n : ℤ) + 4 + (n : ℤ) * (-1) ^ n := by
  subst h
  have hs : (-1 : ℤ) ^ (2 * m + 2) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
  rw [a_even, hs]
  push_cast
  ring

lemma closed_odd (n m : ℕ) (h : n = 2 * m + 3) :
    4 * a n = 2 * (n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 9 * (n : ℤ) + 4 + (n : ℤ) * (-1) ^ n := by
  subst h
  have hs : (-1 : ℤ) ^ (2 * m + 3) = -1 := Odd.neg_one_pow ⟨m + 1, by ring⟩
  rw [a_odd, hs]
  push_cast
  ring

lemma closed (n : ℕ) :
    4 * a n = 2 * (n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 9 * (n : ℤ) + 4 + (n : ℤ) * (-1) ^ n := by
  rcases Nat.even_or_odd n with ⟨c, hc⟩ | ⟨c, hc⟩
  · rcases c with _ | c
    · have h0 : n = 0 := by omega
      subst h0
      have ha : a 0 = 1 := by decide
      rw [ha]
      norm_num
    · exact closed_even n c (by omega)
  · rcases c with _ | c
    · have h1 : n = 1 := by omega
      subst h1
      have ha : a 1 = 5 := by decide
      rw [ha]
      norm_num
    · exact closed_odd n c (by omega)

end OMA.P246697

open OMA.S_oeis_a246697 OMA.P246697 in
theorem OMA.solution : type_of% @OMA.S_oeis_a246697.main := by
  refine ⟨closed, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  have e6 : m + 6 - 6 = m := by omega
  rw [e1, e2, e3, e4, e5, e6]
  have h0 := closed m
  have h1 := closed (m + 1)
  have h2 := closed (m + 2)
  have h3 := closed (m + 3)
  have h4 := closed (m + 4)
  have h5 := closed (m + 5)
  have h6 := closed (m + 6)
  push_cast at h0 h1 h2 h3 h4 h5 h6
  have key : 4 * a (m + 6) = 4 * (2 * a (m + 5) + a (m + 4) - 4 * a (m + 3) + a (m + 2)
      + 2 * a (m + 1) - a m) := by
    linear_combination h6 - 2 * h5 - h4 + 4 * h3 - h2 - 2 * h1 + h0
  linarith
