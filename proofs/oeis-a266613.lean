import OMAStatements.S_oeis_a266613

open OMA.S_oeis_a266613

def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, tail => tail
  | k + 1, tail => w ++ blocks w k tail

lemma blocks_append (w : List Bool) (k : ℕ) (u v : List Bool) :
    blocks w k u ++ v = blocks w k (u ++ v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

def word0 (k : ℕ) : List Bool :=
  blocks [false, false, false, false, false, false, false, false] k ([false, false, false, false, false, false, false, false, true])

def word1 (k : ℕ) : List Bool :=
  blocks [true, true, true, true, true, true, true, true] k ([true, true, true, true, true, true, true, true, false, false, false])

def word2 (k : ℕ) : List Bool :=
  blocks [false, false, false, false, false, false, false, false] k ([false, false, false, false, false, false, false, false, false, false, true, false, true])

def word3 (k : ℕ) : List Bool :=
  blocks [true, true, true, true, true, true, true, true] k ([true, true, true, true, true, true, true, true, true, true, false, false, true, false, false])

lemma align1 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false, false, false, false, false, false] (k + 1) tail =
      [false, false] ++ blocks [false, false, false, false, false, false, false, false] k ([false, false, false, false, false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false, false, false, false, false, false] ++ rest) ih

lemma align2 (k : ℕ) (tail : List Bool) :
    blocks [true, true, true, true, true, true, true, true] (k + 1) tail =
      [true, true] ++ blocks [true, true, true, true, true, true, true, true] k ([true, true, true, true, true, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true, true, true, true, true, true, true] ++ rest) ih

lemma scanBlock1 (k : ℕ) (tail : List Bool) :
    scan false false (blocks [false, false, false, false, false, false, false, false] k tail) =
      blocks [true, true, true, true, true, true, true, true] k (scan false false tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true, true, true, true, true, true, true, true] ++ rest) ih

lemma scanBlock2 (k : ℕ) (tail : List Bool) :
    scan true true (blocks [true, true, true, true, true, true, true, true] k tail) =
      blocks [false, false, false, false, false, false, false, false] k (scan true true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false, false, false, false, false, false, false, false] ++ rest) ih

lemma align3 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false, false, false, false, false, false] (k + 2) tail =
      [false, false] ++ blocks [false, false, false, false, false, false, false, false] k ([false, false, false, false, false, false, false, false, false, false, false, false, false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false, false, false, false, false, false] ++ rest) ih

lemma phase0 (k : ℕ) :
    scan false false ((word0 k) ++ [false, false]) =
      word1 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word0, word1, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan false false (blocks [false, false, false, false, false, false, false, false] (k + 1) ([false, false, false, false, false, false, false, false, true] ++ [false, false])) = blocks [true, true, true, true, true, true, true, true] (k + 1) ([true, true, true, true, true, true, true, true, false, false, false])
    conv => lhs; rw [align1]
    conv => rhs; rw [align2]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1]
    <;> rfl

lemma phase1 (k : ℕ) :
    scan true true ((word1 k) ++ [true, true]) =
      word2 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word1, word2, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan true true (blocks [true, true, true, true, true, true, true, true] (k + 1) ([true, true, true, true, true, true, true, true, false, false, false] ++ [true, true])) = blocks [false, false, false, false, false, false, false, false] (k + 1) ([false, false, false, false, false, false, false, false, false, false, true, false, true])
    conv => lhs; rw [align2]
    conv => rhs; rw [align1]
    simp only [List.cons_append, List.nil_append, scan, scanBlock2]
    <;> rfl

lemma phase2 (k : ℕ) :
    scan false false ((word2 k) ++ [false, false]) =
      word3 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word2, word3, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan false false (blocks [false, false, false, false, false, false, false, false] (k + 1) ([false, false, false, false, false, false, false, false, false, false, true, false, true] ++ [false, false])) = blocks [true, true, true, true, true, true, true, true] (k + 1) ([true, true, true, true, true, true, true, true, true, true, false, false, true, false, false])
    conv => lhs; rw [align1]
    conv => rhs; rw [align2]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1]
    <;> rfl

lemma phase3 (k : ℕ) :
    scan true true ((word3 k) ++ [true, true]) =
      word0 (k + 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word3, word0, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan true true (blocks [true, true, true, true, true, true, true, true] (k + 1) ([true, true, true, true, true, true, true, true, true, true, false, false, true, false, false] ++ [true, true])) = blocks [false, false, false, false, false, false, false, false] (k + 2) ([false, false, false, false, false, false, false, false, true])
    conv => lhs; rw [align2]
    conv => rhs; rw [align3]
    simp only [List.cons_append, List.nil_append, scan, scanBlock2]
    <;> rfl

lemma cycle (k : ℕ) :
    (row (4 * k + 4) = word0 k ∧ background (4 * k + 4) = false) ∧
    (row (4 * k + 5) = word1 k ∧ background (4 * k + 5) = true) ∧
    (row (4 * k + 6) = word2 k ∧ background (4 * k + 6) = false) ∧
    (row (4 * k + 7) = word3 k ∧ background (4 * k + 7) = true) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h0 : row (4 * (k + 1) + 4) = word0 (k+1) ∧ background (4 * (k + 1) + 4) = false := by
      rw [show 4 * (k + 1) + 4 = (4 * k + 7) + 1 by omega]
      exact ⟨by rw [row, ih.2.2.2.1, ih.2.2.2.2]; exact phase3 k, by rw [background, ih.2.2.2.2]; rfl⟩
    have h1 : row (4 * (k + 1) + 5) = word1 (k+1) ∧ background (4 * (k + 1) + 5) = true := by
      rw [show 4 * (k + 1) + 5 = (4 * (k + 1) + 4) + 1 by omega]
      exact ⟨by rw [row, h0.1, h0.2]; exact phase0 (k + 1), by rw [background, h0.2]; rfl⟩
    have h2 : row (4 * (k + 1) + 6) = word2 (k+1) ∧ background (4 * (k + 1) + 6) = false := by
      rw [show 4 * (k + 1) + 6 = (4 * (k + 1) + 5) + 1 by omega]
      exact ⟨by rw [row, h1.1, h1.2]; exact phase1 (k + 1), by rw [background, h1.2]; rfl⟩
    have h3 : row (4 * (k + 1) + 7) = word3 (k+1) ∧ background (4 * (k + 1) + 7) = true := by
      rw [show 4 * (k + 1) + 7 = (4 * (k + 1) + 6) + 1 by omega]
      exact ⟨by rw [row, h2.1, h2.2]; exact phase2 (k + 1), by rw [background, h2.2]; rfl⟩
    exact ⟨h0, h1, h2, h3⟩


lemma block_lookup (w tail : List Bool) (k j : ℕ) :
    (blocks w k tail)[j]? =
      if j < k * w.length then w[j % w.length]? else tail[j - k * w.length]? := by
  induction k generalizing j with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, List.getElem?_append, Nat.succ_mul]
    split_ifs with h₁ h₂ h₂
    · rw [Nat.mod_eq_of_lt h₁]
    · omega
    · rw [ih, if_pos (by omega)]
      congr 1
      exact (Nat.mod_eq_sub_mod (by omega : w.length ≤ j)).symm
    · rw [ih, if_neg (by omega), Nat.sub_sub, Nat.add_comm]

lemma centerValue0 (k : ℕ) : center (4 * k + 4) = 0 := by
  rw [center, (cycle k).1.1, word0]
  by_cases small : k < 2
  · interval_cases k <;> rfl
  rw [block_lookup, if_pos (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, List.getElem?_cons, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

lemma centerValue1 (k : ℕ) : center (4 * k + 5) = 1 := by
  rw [center, (cycle k).2.1.1, word1]
  by_cases small : k < 2
  · interval_cases k <;> rfl
  rw [block_lookup, if_pos (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, List.getElem?_cons, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

lemma centerValue2 (k : ℕ) : center (4 * k + 6) = 0 := by
  rw [center, (cycle k).2.2.1.1, word2]
  by_cases small : k < 2
  · interval_cases k <;> rfl
  rw [block_lookup, if_pos (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, List.getElem?_cons, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

lemma centerValue3 (k : ℕ) : center (4 * k + 7) = 1 := by
  rw [center, (cycle k).2.2.2.1, word3]
  by_cases small : k < 2
  · interval_cases k <;> rfl
  rw [block_lookup, if_pos (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, List.getElem?_cons, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

lemma values (k : ℕ) :
    ((a (4 * k + 4) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ k) ∧
    ((a (4 * k + 5) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ k) ∧
    ((a (4 * k + 6) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ k) ∧
    ((a (4 * k + 7) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k) := by
  induction k with
  | zero => norm_num [show a 4 = 20 by rfl, show a 5 = 41 by rfl, show a 6 = 82 by rfl, show a 7 = 165 by rfl]
  | succ k ih =>
    have h0 : (a (4 * (k+1) + 4) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k+1) := by
      have hs : 4 * (k+1) + 4 = (4 * k + 7) + 1 := by omega
      rw [hs, a, ← hs, centerValue0]
      push_cast
      rw [ih.2.2.2]
      push_cast
      simp only [pow_succ]
      ring
    have h1 : (a (4 * (k+1) + 5) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ (k+1) := by
      have hs : 4 * (k+1) + 5 = (4 * (k+1) + 4) + 1 := by omega
      rw [hs, a, ← hs, centerValue1]
      push_cast
      rw [h0]
      push_cast
      simp only [pow_succ]
      ring
    have h2 : (a (4 * (k+1) + 6) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ (k+1) := by
      have hs : 4 * (k+1) + 6 = (4 * (k+1) + 5) + 1 := by omega
      rw [hs, a, ← hs, centerValue2]
      push_cast
      rw [h1]
      push_cast
      simp only [pow_succ]
      ring
    have h3 : (a (4 * (k+1) + 7) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ (k+1) := by
      have hs : 4 * (k+1) + 7 = (4 * (k+1) + 6) + 1 := by omega
      rw [hs, a, ← hs, centerValue3]
      push_cast
      rw [h2]
      push_cast
      simp only [pow_succ]
      ring
    exact ⟨h0, h1, h2, h3⟩
lemma value0 (k : ℕ) : (a (4 * k + 4) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ k := (values k).1
lemma value1 (k : ℕ) : (a (4 * k + 5) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ k := (values k).2.1
lemma value2 (k : ℕ) : (a (4 * k + 6) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ k := (values k).2.2.1
lemma value3 (k : ℕ) : (a (4 * k + 7) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k := (values k).2.2.2

lemma initial0 : a 0 = 1 := by rfl
lemma initial1 : a 1 = 2 := by rfl
lemma initial2 : a 2 = 5 := by rfl
lemma initial3 : a 3 = 10 := by rfl
lemma initial4 : a 4 = 20 := by rfl
lemma initial5 : a 5 = 41 := by rfl
lemma initial6 : a 6 = 82 := by rfl
lemma initial7 : a 7 = 165 := by rfl

lemma claim1 : ∀ n : ℕ, 2 < n → (a n : ℚ) = (31 * 2 ^ n - 4 * ((-1) ^ n + 3)) / 24 := by
  intro n hn
  by_cases small : n < 4
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 4 ∨ n = 4 * k + 5 ∨ n = 4 * k + 6 ∨ n = 4 * k + 7 := by
    exact ⟨(n - 4) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ k := by
      rw [show n = 4 * k + 4 by omega]
      exact value0 k
    have power1 : (2 : ℚ) ^ n = (16 : ℚ) ^ k * (2 : ℚ) ^ 4 := by
      rw [show n = 4 * k + 4 by omega, pow_add, pow_mul]
      norm_num
    have power2 : (-1 : ℚ) ^ n = (1 : ℚ) ^ k * (-1 : ℚ) ^ 4 := by
      rw [show n = 4 * k + 4 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1, power2]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ k := by
      rw [show n = 4 * k + 5 by omega]
      exact value1 k
    have power1 : (2 : ℚ) ^ n = (16 : ℚ) ^ k * (2 : ℚ) ^ 5 := by
      rw [show n = 4 * k + 5 by omega, pow_add, pow_mul]
      norm_num
    have power2 : (-1 : ℚ) ^ n = (1 : ℚ) ^ k * (-1 : ℚ) ^ 5 := by
      rw [show n = 4 * k + 5 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1, power2]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ k := by
      rw [show n = 4 * k + 6 by omega]
      exact value2 k
    have power1 : (2 : ℚ) ^ n = (16 : ℚ) ^ k * (2 : ℚ) ^ 6 := by
      rw [show n = 4 * k + 6 by omega, pow_add, pow_mul]
      norm_num
    have power2 : (-1 : ℚ) ^ n = (1 : ℚ) ^ k * (-1 : ℚ) ^ 6 := by
      rw [show n = 4 * k + 6 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1, power2]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k := by
      rw [show n = 4 * k + 7 by omega]
      exact value3 k
    have power1 : (2 : ℚ) ^ n = (16 : ℚ) ^ k * (2 : ℚ) ^ 7 := by
      rw [show n = 4 * k + 7 by omega, pow_add, pow_mul]
      norm_num
    have power2 : (-1 : ℚ) ^ n = (1 : ℚ) ^ k * (-1 : ℚ) ^ 7 := by
      rw [show n = 4 * k + 7 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1, power2]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring

lemma claim2 : ∀ n : ℕ, 5 < n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) + (a (n - 2) : ℤ) - 2 * (a (n - 3) : ℤ) := by
  intro n hn
  suffices hq : (a n : ℚ) = 2 * (a (n - 1) : ℚ) + (a (n - 2) : ℚ) - 2 * (a (n - 3) : ℚ) by exact_mod_cast hq
  by_cases small : n < 8
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 8 ∨ n = 4 * k + 9 ∨ n = 4 * k + 10 ∨ n = 4 * k + 11 := by
    exact ⟨(n - 8) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v1 : (a (n - 2) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 2 = 4 * k + 6 by omega]
      exact value2 k
    have v2 : (a (n - 3) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 3 = 4 * k + 5 by omega]
      exact value1 k
    have v3 : (a (n - 1) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 1 = 4 * k + 7 by omega]
      exact value3 k
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    have v1 : (a (n - 2) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 2 = 4 * k + 7 by omega]
      exact value3 k
    have v2 : (a (n - 3) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 3 = 4 * k + 6 by omega]
      exact value2 k
    have v3 : (a (n - 1) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 1 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    have v1 : (a (n - 2) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 2 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v2 : (a (n - 3) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 3 = 4 * k + 7 by omega]
      exact value3 k
    have v3 : (a (n - 1) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 1 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    have v1 : (a (n - 2) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 2 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    have v2 : (a (n - 3) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 3 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v3 : (a (n - 1) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 1 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring

lemma claim3Tail : ∀ n : ℕ, 5 < n → (a n : ℚ) = -(2 * (a (n - 3) : ℚ) + -1 * (a (n - 2) : ℚ) + -2 * (a (n - 1) : ℚ)) := by
  intro n hn
  by_cases small : n < 8
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 8 ∨ n = 4 * k + 9 ∨ n = 4 * k + 10 ∨ n = 4 * k + 11 := by
    exact ⟨(n - 8) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v1 : (a (n - 1) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 1 = 4 * k + 7 by omega]
      exact value3 k
    have v2 : (a (n - 3) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 3 = 4 * k + 5 by omega]
      exact value1 k
    have v3 : (a (n - 2) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 2 = 4 * k + 6 by omega]
      exact value2 k
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    have v1 : (a (n - 1) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 1 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v2 : (a (n - 3) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 3 = 4 * k + 6 by omega]
      exact value2 k
    have v3 : (a (n - 2) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 2 = 4 * k + 7 by omega]
      exact value3 k
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    have v1 : (a (n - 1) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 1 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    have v2 : (a (n - 3) : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ k := by
      rw [show n - 3 = 4 * k + 7 by omega]
      exact value3 k
    have v3 : (a (n - 2) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 2 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 3) + (496 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    have v1 : (a (n - 1) : ℚ) = (-2 / 3) + (248 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 1 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    have v2 : (a (n - 3) : ℚ) = (-2 / 3) + (62 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 3 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v3 : (a (n - 2) : ℚ) = (-1 / 3) + (124 / 3) * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 2 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p16]
      all_goals ring

open PowerSeries in
lemma claim3 : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X)) = 1 - X ^ 4 + X ^ 5 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  have hd : s * ((1 - X) * (1 + X) * (1 - 2 * X)) = PowerSeries.C (1 : ℚ) * (s * X ^ 0) + PowerSeries.C (-2 : ℚ) * (s * X ^ 1) + PowerSeries.C (-1 : ℚ) * (s * X ^ 2) + PowerSeries.C (2 : ℚ) * (s * X ^ 3) := by norm_num [map_ofNat] <;> ring
  have hn : 1 - X ^ 4 + X ^ 5 = PowerSeries.C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ) + PowerSeries.C (-1 : ℚ) * (X ^ 4 : PowerSeries ℚ) + PowerSeries.C (1 : ℚ) * (X ^ 5 : PowerSeries ℚ) := by norm_num [map_ofNat] <;> ring
  rw [hd, hn]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_X_pow, coeff_mul_X_pow', s, coeff_mk]
  by_cases h : n ≤ 5
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5]
  · have hr := claim3Tail n (by omega)
    simp only [if_pos (show 3 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 1 ≤ n by omega), if_pos (show 0 ≤ n by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 5 by omega), Nat.sub_zero]
    linarith


lemma alternatingPair (k : ℕ) :
    3*(a000975 (2*k) : ℚ) = 2*4^k-2 ∧
    3*(a000975 (2*k+1) : ℚ) = 4*4^k-1 := by
  induction k with
  | zero => norm_num [a000975]
  | succ k ih =>
    have h₀ : a000975 (2*(k+1)) = 2*a000975 (2*k+1) := by
      rw [show 2*(k+1) = (2*k+1)+1 by omega, a000975]
      omega
    have h₁ : a000975 (2*(k+1)+1) = 2*a000975 (2*(k+1))+1 := by
      rw [a000975]
      omega
    rw [h₁, h₀, pow_succ]
    push_cast
    constructor <;> linarith [ih.2]

lemma claim4 : ∀ n : ℕ, 2 < n → (a n : ℚ) = (a000975 n : ℚ) + 20 * (2 : ℚ) ^ ((n : ℤ) - 5) := by
  intro n hn
  rw [claim1 n hn, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
  obtain ⟨k, hk | hk⟩ : ∃ k : ℕ, n = 2*k ∨ n = 2*k+1 := by
    exact ⟨n/2, by omega⟩
  · subst n
    norm_num [pow_add, pow_mul]
    linarith [(alternatingPair k).1]
  · subst n
    norm_num [pow_add, pow_mul]
    linarith [(alternatingPair k).2]

theorem OMA.solution : type_of% @OMA.S_oeis_a266613.main := by
  exact ⟨claim1, claim2, claim3, claim4⟩
