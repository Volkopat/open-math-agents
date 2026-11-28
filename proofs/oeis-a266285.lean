import OMAStatements.S_oeis_a266285

open OMA.S_oeis_a266285

def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, tail => tail
  | k + 1, tail => w ++ blocks w k tail

lemma blocks_append (w : List Bool) (k : ℕ) (u v : List Bool) :
    blocks w k u ++ v = blocks w k (u ++ v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

def word0 (k : ℕ) : List Bool :=
  blocks [false, false] k ([false, false, true, false, true] ++ blocks [false, true] k [])

def word1 (k : ℕ) : List Bool :=
  blocks [true, true] k ([true, true, false, true, false, true, false] ++ blocks [true, false] k [])

lemma align1 (k : ℕ) (tail : List Bool) :
    blocks [false, false] (k + 2) tail =
      [false, false] ++ blocks [false, false] k ([false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false] ++ rest) ih

lemma align2 (k : ℕ) (tail : List Bool) :
    blocks [false, true] (k + 2) tail =
      [false, true, false, true] ++ blocks [false, true] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, true] ++ rest) ih

lemma align3 (k : ℕ) (tail : List Bool) :
    blocks [true, true] (k + 2) tail =
      [true, true] ++ blocks [true, true] k ([true, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true] ++ rest) ih

lemma align4 (k : ℕ) (tail : List Bool) :
    blocks [true, false] (k + 2) tail =
      [true, false] ++ blocks [true, false] k ([true, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, false] ++ rest) ih

lemma scanBlock1 (k : ℕ) (tail : List Bool) :
    scan false false (blocks [false, false] k tail) =
      blocks [true, true] k (scan false false tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true, true] ++ rest) ih

lemma scanBlock2 (k : ℕ) (tail : List Bool) :
    scan false true (blocks [false, true] k tail) =
      blocks [true, false] k (scan false true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true, false] ++ rest) ih

lemma align5 (k : ℕ) (tail : List Bool) :
    blocks [true, true] (k + 1) tail =
      [true, true] ++ blocks [true, true] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true] ++ rest) ih

lemma align6 (k : ℕ) (tail : List Bool) :
    blocks [true, false] (k + 1) tail =
      [true, false] ++ blocks [true, false] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, false] ++ rest) ih

lemma align7 (k : ℕ) (tail : List Bool) :
    blocks [false, true] (k + 2) tail =
      [false, true] ++ blocks [false, true] k ([false, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, true] ++ rest) ih

lemma scanBlock3 (k : ℕ) (tail : List Bool) :
    scan true true (blocks [true, true] k tail) =
      blocks [false, false] k (scan true true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false, false] ++ rest) ih

lemma scanBlock4 (k : ℕ) (tail : List Bool) :
    scan true false (blocks [true, false] k tail) =
      blocks [false, true] k (scan true false tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false, true] ++ rest) ih

lemma phase0 (k : ℕ) :
    scan false false ((word0 k) ++ [false, false]) =
      word1 k := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [word0, word1, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
      change scan false false (blocks [false, false] (k + 2) ([false, false, true, false, true] ++ blocks [false, true] (k + 2) ([false, false]))) = blocks [true, true] (k + 2) ([true, true, false, true, false, true, false] ++ blocks [true, false] (k + 2) [])
      conv => lhs; rw [align1]
      conv => lhs; rw [align2]
      conv => rhs; rw [align3]
      conv => rhs; rw [align4]
      simp only [List.cons_append, List.nil_append, scan, scanBlock1, scanBlock2]
      <;> rfl

lemma phase1 (k : ℕ) :
    scan true true ((word1 k) ++ [true, true]) =
      word0 (k + 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word1, word0, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan true true (blocks [true, true] (k + 1) ([true, true, false, true, false, true, false] ++ blocks [true, false] (k + 1) ([true, true]))) = blocks [false, false] (k + 2) ([false, false, true, false, true] ++ blocks [false, true] (k + 2) [])
    conv => lhs; rw [align5]
    conv => lhs; rw [align6]
    conv => rhs; rw [align1]
    conv => rhs; rw [align7]
    simp only [List.cons_append, List.nil_append, scan, scanBlock3, scanBlock4]
    <;> rfl

lemma cycle (k : ℕ) :
    (row (2 * k + 2) = word0 k ∧ background (2 * k + 2) = false) ∧
    (row (2 * k + 3) = word1 k ∧ background (2 * k + 3) = true) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h0 : row (2 * (k + 1) + 2) = word0 (k+1) ∧ background (2 * (k + 1) + 2) = false := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by omega]
      exact ⟨by rw [row, ih.2.1, ih.2.2]; exact phase1 k, by rw [background, ih.2.2]; rfl⟩
    have h1 : row (2 * (k + 1) + 3) = word1 (k+1) ∧ background (2 * (k + 1) + 3) = true := by
      rw [show 2 * (k + 1) + 3 = (2 * (k + 1) + 2) + 1 by omega]
      exact ⟨by rw [row, h0.1, h0.2]; exact phase0 (k + 1), by rw [background, h0.2]; rfl⟩
    exact ⟨h0, h1⟩

lemma block_count (c : Bool) (w : List Bool) (k : ℕ) (tail : List Bool) :
    (blocks w k tail).count c = k * w.count c + tail.count c := by
  induction k with
  | zero => simp [blocks]
  | succ k ih => rw [blocks, List.count_append, ih, Nat.succ_mul]; omega

lemma rowCount0 (k : ℕ) : (row (2 * k + 2)).count true = 1 * k + 2 := by
  rw [(cycle k).1.1]
  simp [word0, List.count_append, block_count, List.count_cons] <;> omega

lemma value0 (k : ℕ) : (a (2 * k + 2) : ℚ) = 2 + ((k : ℕ) : ℚ) := by
  change ((row (2 * k + 2)).count true : ℚ) = _
  rw [rowCount0]
  push_cast
  ring

lemma rowCount1 (k : ℕ) : (row (2 * k + 3)).count true = 3 * k + 4 := by
  rw [(cycle k).2.1]
  simp [word1, List.count_append, block_count, List.count_cons] <;> omega

lemma value1 (k : ℕ) : (a (2 * k + 3) : ℚ) = 4 + 3 * ((k : ℕ) : ℚ) := by
  change ((row (2 * k + 3)).count true : ℚ) = _
  rw [rowCount1]
  push_cast
  ring


lemma initial0 : a 0 = 1 := by rfl
lemma initial1 : a 1 = 1 := by rfl
lemma initial2 : a 2 = 2 := by rfl
lemma initial3 : a 3 = 4 := by rfl
lemma initial4 : a 4 = 3 := by rfl
lemma initial5 : a 5 = 7 := by rfl

lemma claim1 : ∀ n : ℕ, (a n : ℚ) = ((-1) ^ n * (3 - 2 * (n : ℚ)) + 4 * (n : ℚ) + 1) / 4 := by
  intro n
  by_cases small : n < 2
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial0, initial1] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    exact ⟨(n - 2) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 2 + ((k : ℕ) : ℚ) := by
      rw [show n = 2 * k + 2 by omega]
      exact value0 k
    have power1 : (-1 : ℚ) ^ n = (1 : ℚ) ^ k * (-1 : ℚ) ^ 2 := by
      rw [show n = 2 * k + 2 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring
  · have v0 : (a n : ℚ) = 4 + 3 * ((k : ℕ) : ℚ) := by
      rw [show n = 2 * k + 3 by omega]
      exact value1 k
    have power1 : (-1 : ℚ) ^ n = (1 : ℚ) ^ k * (-1 : ℚ) ^ 3 := by
      rw [show n = 2 * k + 3 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring

lemma claim2 : ∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  intro n hn
  suffices hq : (a n : ℚ) = 2 * (a (n - 2) : ℚ) - (a (n - 4) : ℚ) by exact_mod_cast hq
  by_cases small : n < 6
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial0, initial1, initial2, initial3, initial4, initial5] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 6 ∨ n = 2 * k + 7 := by
    exact ⟨(n - 6) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 2 + ((k + 2 : ℕ) : ℚ) := by
      rw [show n = 2 * (k + 2) + 2 by omega]
      exact value0 (k + 2)
    have v1 : (a (n - 4) : ℚ) = 2 + ((k : ℕ) : ℚ) := by
      rw [show n - 4 = 2 * k + 2 by omega]
      exact value0 k
    have v2 : (a (n - 2) : ℚ) = 2 + ((k + 1 : ℕ) : ℚ) := by
      rw [show n - 2 = 2 * (k + 1) + 2 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring
  · have v0 : (a n : ℚ) = 4 + 3 * ((k + 2 : ℕ) : ℚ) := by
      rw [show n = 2 * (k + 2) + 3 by omega]
      exact value1 (k + 2)
    have v1 : (a (n - 4) : ℚ) = 4 + 3 * ((k : ℕ) : ℚ) := by
      rw [show n - 4 = 2 * k + 3 by omega]
      exact value1 k
    have v2 : (a (n - 2) : ℚ) = 4 + 3 * ((k + 1 : ℕ) : ℚ) := by
      rw [show n - 2 = 2 * (k + 1) + 3 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring

lemma claim3Tail : ∀ n : ℕ, 3 < n → (a n : ℚ) = -(1 * (a (n - 4) : ℚ) + -2 * (a (n - 2) : ℚ)) := by
  intro n hn
  by_cases small : n < 6
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial0, initial1, initial2, initial3, initial4, initial5] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 6 ∨ n = 2 * k + 7 := by
    exact ⟨(n - 6) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 2 + ((k + 2 : ℕ) : ℚ) := by
      rw [show n = 2 * (k + 2) + 2 by omega]
      exact value0 (k + 2)
    have v1 : (a (n - 4) : ℚ) = 2 + ((k : ℕ) : ℚ) := by
      rw [show n - 4 = 2 * k + 2 by omega]
      exact value0 k
    have v2 : (a (n - 2) : ℚ) = 2 + ((k + 1 : ℕ) : ℚ) := by
      rw [show n - 2 = 2 * (k + 1) + 2 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring
  · have v0 : (a n : ℚ) = 4 + 3 * ((k + 2 : ℕ) : ℚ) := by
      rw [show n = 2 * (k + 2) + 3 by omega]
      exact value1 (k + 2)
    have v1 : (a (n - 4) : ℚ) = 4 + 3 * ((k : ℕ) : ℚ) := by
      rw [show n - 4 = 2 * k + 3 by omega]
      exact value1 k
    have v2 : (a (n - 2) : ℚ) = 4 + 3 * ((k + 1 : ℕ) : ℚ) := by
      rw [show n - 2 = 2 * (k + 1) + 3 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring

open PowerSeries in
lemma claim3 : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) = 1 + X + 2 * X ^ 3 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  have hd : s * ((1 - X) ^ 2 * (1 + X) ^ 2) = PowerSeries.C (1 : ℚ) * (s * X ^ 0) + PowerSeries.C (-2 : ℚ) * (s * X ^ 2) + PowerSeries.C (1 : ℚ) * (s * X ^ 4) := by norm_num [map_ofNat] <;> ring
  have hn : 1 + X + 2 * X ^ 3 = PowerSeries.C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ) + PowerSeries.C (1 : ℚ) * (X ^ 1 : PowerSeries ℚ) + PowerSeries.C (2 : ℚ) * (X ^ 3 : PowerSeries ℚ) := by norm_num [map_ofNat] <;> ring
  rw [hd, hn]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_X_pow, coeff_mul_X_pow', s, coeff_mk]
  by_cases h : n ≤ 3
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3]
  · have hr := claim3Tail n (by omega)
    simp only [if_pos (show 4 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 0 ≤ n by omega), if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 3 by omega), Nat.sub_zero]
    linarith

lemma claim4 : ∀ n : ℕ, (a (2 * n) : ℤ) = (n : ℤ) + 1 := by
  intro n
  suffices hq : (a (2 * n) : ℚ) = (n : ℚ) + 1 by exact_mod_cast hq
  by_cases small : n < 2
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial0, initial2] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    exact ⟨(n - 2) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a (2 * n) : ℚ) = 2 + ((2 * k + 1 : ℕ) : ℚ) := by
      rw [show 2 * n = 2 * (2 * k + 1) + 2 by omega]
      exact value0 (2 * k + 1)
    simp only [v0]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring
  · have v0 : (a (2 * n) : ℚ) = 2 + ((2 * k + 2 : ℕ) : ℚ) := by
      rw [show 2 * n = 2 * (2 * k + 2) + 2 by omega]
      exact value0 (2 * k + 2)
    simp only [v0]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring

lemma claim5 : ∀ n : ℕ, (a (2 * n + 1) : ℤ) = 3 * (n : ℤ) + 1 := by
  intro n
  suffices hq : (a (2 * n + 1) : ℚ) = 3 * (n : ℚ) + 1 by exact_mod_cast hq
  by_cases small : n < 2
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, initial1, initial3] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    exact ⟨(n - 2) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a (2 * n + 1) : ℚ) = 4 + 3 * ((2 * k + 1 : ℕ) : ℚ) := by
      rw [show 2 * n + 1 = 2 * (2 * k + 1) + 3 by omega]
      exact value1 (2 * k + 1)
    simp only [v0]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring
  · have v0 : (a (2 * n + 1) : ℚ) = 4 + 3 * ((2 * k + 2 : ℕ) : ℚ) := by
      rw [show 2 * n + 1 = 2 * (2 * k + 2) + 3 by omega]
      exact value1 (2 * k + 2)
    simp only [v0]
    try rw [hk]
    push_cast
    norm_num [pow_succ, pow_add, pow_mul]
    all_goals try simp only [one_pow]
    all_goals ring

theorem OMA.solution : type_of% @OMA.S_oeis_a266285.main := by
  exact ⟨claim1, claim2, claim3, claim4, claim5⟩
