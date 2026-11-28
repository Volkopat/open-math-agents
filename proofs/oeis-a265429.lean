import OMAStatements.S_oeis_a265429

open OMA.S_oeis_a265429

def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, tail => tail
  | k + 1, tail => w ++ blocks w k tail

lemma blocks_append (w : List Bool) (k : ℕ) (u v : List Bool) :
    blocks w k u ++ v = blocks w k (u ++ v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

def word0 (k : ℕ) : List Bool :=
  blocks [false, false, false, false] k ([false, false, false, false, true, true, true, false, true] ++ blocks [true, true, false, true] k [])

def word1 (k : ℕ) : List Bool :=
  blocks [false, false, false, false] k ([false, false, false, false, false, true, true, false, true, true, true] ++ blocks [false, true, true, true] k [])

def word2 (k : ℕ) : List Bool :=
  blocks [false, false, false, false] k ([false, false, false, false, false, false, true, false, true, true, true, false, true] ++ blocks [true, true, false, true] k [])

def word3 (k : ℕ) : List Bool :=
  blocks [false, false, false, false] k ([false, false, false, false, false, false, false, true, true, true, true, false, true, true, true] ++ blocks [false, true, true, true] k [])

lemma align1 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false, false] (k + 1) tail =
      [false, false] ++ blocks [false, false, false, false] k ([false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false, false] ++ rest) ih

lemma align2 (k : ℕ) (tail : List Bool) :
    blocks [true, true, false, true] (k + 1) tail =
      [true, true, false, true] ++ blocks [true, true, false, true] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true, false, true] ++ rest) ih

lemma align3 (k : ℕ) (tail : List Bool) :
    blocks [false, true, true, true] (k + 1) tail =
      [false, true] ++ blocks [true, true, false, true] k ([true, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, true, true, true] ++ rest) ih

lemma scanBlock1 (k : ℕ) (tail : List Bool) :
    scan false false (blocks [false, false, false, false] k tail) =
      blocks [false, false, false, false] k (scan false false tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false, false, false, false] ++ rest) ih

lemma scanBlock2 (k : ℕ) (tail : List Bool) :
    scan false true (blocks [true, true, false, true] k tail) =
      blocks [true, true, false, true] k (scan false true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true, true, false, true] ++ rest) ih

lemma align4 (k : ℕ) (tail : List Bool) :
    blocks [false, true, true, true] (k + 1) tail =
      [false, true, true, true] ++ blocks [false, true, true, true] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, true, true, true] ++ rest) ih

lemma align5 (k : ℕ) (tail : List Bool) :
    blocks [true, true, false, true] (k + 1) tail =
      [true, true] ++ blocks [false, true, true, true] k ([false, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true, false, true] ++ rest) ih

lemma scanBlock3 (k : ℕ) (tail : List Bool) :
    scan true true (blocks [false, true, true, true] k tail) =
      blocks [false, true, true, true] k (scan true true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false, true, true, true] ++ rest) ih

lemma align6 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false, false] (k + 2) tail =
      [false, false] ++ blocks [false, false, false, false] k ([false, false, false, false, false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false, false] ++ rest) ih

lemma align7 (k : ℕ) (tail : List Bool) :
    blocks [true, true, false, true] (k + 2) tail =
      [true, true, false, true] ++ blocks [true, true, false, true] k ([true, true, false, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true, false, true] ++ rest) ih

lemma phase0 (k : ℕ) :
    scan false false ((word0 k) ++ [false, false]) =
      word1 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word0, word1, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan false false (blocks [false, false, false, false] (k + 1) ([false, false, false, false, true, true, true, false, true] ++ blocks [true, true, false, true] (k + 1) ([false, false]))) = blocks [false, false, false, false] (k + 1) ([false, false, false, false, false, true, true, false, true, true, true] ++ blocks [false, true, true, true] (k + 1) [])
    conv => lhs; rw [align1]
    conv => lhs; rw [align2]
    conv => rhs; rw [align1]
    conv => rhs; rw [align3]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1, scanBlock2]
    <;> rfl

lemma phase1 (k : ℕ) :
    scan false false ((word1 k) ++ [false, false]) =
      word2 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word1, word2, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan false false (blocks [false, false, false, false] (k + 1) ([false, false, false, false, false, true, true, false, true, true, true] ++ blocks [false, true, true, true] (k + 1) ([false, false]))) = blocks [false, false, false, false] (k + 1) ([false, false, false, false, false, false, true, false, true, true, true, false, true] ++ blocks [true, true, false, true] (k + 1) [])
    conv => lhs; rw [align1]
    conv => lhs; rw [align4]
    conv => rhs; rw [align1]
    conv => rhs; rw [align5]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1, scanBlock3]
    <;> rfl

lemma phase2 (k : ℕ) :
    scan false false ((word2 k) ++ [false, false]) =
      word3 k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word2, word3, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan false false (blocks [false, false, false, false] (k + 1) ([false, false, false, false, false, false, true, false, true, true, true, false, true] ++ blocks [true, true, false, true] (k + 1) ([false, false]))) = blocks [false, false, false, false] (k + 1) ([false, false, false, false, false, false, false, true, true, true, true, false, true, true, true] ++ blocks [false, true, true, true] (k + 1) [])
    conv => lhs; rw [align1]
    conv => lhs; rw [align2]
    conv => rhs; rw [align1]
    conv => rhs; rw [align3]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1, scanBlock2]
    <;> rfl

lemma phase3 (k : ℕ) :
    scan false false ((word3 k) ++ [false, false]) =
      word0 (k + 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word3, word0, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan false false (blocks [false, false, false, false] (k + 1) ([false, false, false, false, false, false, false, true, true, true, true, false, true, true, true] ++ blocks [false, true, true, true] (k + 1) ([false, false]))) = blocks [false, false, false, false] (k + 2) ([false, false, false, false, true, true, true, false, true] ++ blocks [true, true, false, true] (k + 2) [])
    conv => lhs; rw [align1]
    conv => lhs; rw [align3]
    conv => rhs; rw [align6]
    conv => rhs; rw [align7]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1, scanBlock2]
    <;> rfl

lemma cycle (k : ℕ) :
    (row (4 * k + 4) = word0 k ∧ background (4 * k + 4) = false) ∧
    (row (4 * k + 5) = word1 k ∧ background (4 * k + 5) = false) ∧
    (row (4 * k + 6) = word2 k ∧ background (4 * k + 6) = false) ∧
    (row (4 * k + 7) = word3 k ∧ background (4 * k + 7) = false) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h0 : row (4 * (k + 1) + 4) = word0 (k+1) ∧ background (4 * (k + 1) + 4) = false := by
      rw [show 4 * (k + 1) + 4 = (4 * k + 7) + 1 by omega]
      exact ⟨by rw [row, ih.2.2.2.1, ih.2.2.2.2]; exact phase3 k, by rw [background, ih.2.2.2.2]; rfl⟩
    have h1 : row (4 * (k + 1) + 5) = word1 (k+1) ∧ background (4 * (k + 1) + 5) = false := by
      rw [show 4 * (k + 1) + 5 = (4 * (k + 1) + 4) + 1 by omega]
      exact ⟨by rw [row, h0.1, h0.2]; exact phase0 (k + 1), by rw [background, h0.2]; rfl⟩
    have h2 : row (4 * (k + 1) + 6) = word2 (k+1) ∧ background (4 * (k + 1) + 6) = false := by
      rw [show 4 * (k + 1) + 6 = (4 * (k + 1) + 5) + 1 by omega]
      exact ⟨by rw [row, h1.1, h1.2]; exact phase1 (k + 1), by rw [background, h1.2]; rfl⟩
    have h3 : row (4 * (k + 1) + 7) = word3 (k+1) ∧ background (4 * (k + 1) + 7) = false := by
      rw [show 4 * (k + 1) + 7 = (4 * (k + 1) + 6) + 1 by omega]
      exact ⟨by rw [row, h2.1, h2.2]; exact phase2 (k + 1), by rw [background, h2.2]; rfl⟩
    exact ⟨h0, h1, h2, h3⟩

lemma block_count (c : Bool) (w : List Bool) (k : ℕ) (tail : List Bool) :
    (blocks w k tail).count c = k * w.count c + tail.count c := by
  induction k with
  | zero => simp [blocks]
  | succ k ih => rw [blocks, List.count_append, ih, Nat.succ_mul]; omega

lemma rowCount0 (k : ℕ) : (row (4 * k + 4)).count true = 3 * k + 4 := by
  rw [(cycle k).1.1]
  simp [word0, List.count_append, block_count, List.count_cons] <;> omega

lemma rowCount1 (k : ℕ) : (row (4 * k + 5)).count true = 3 * k + 5 := by
  rw [(cycle k).2.1.1]
  simp [word1, List.count_append, block_count, List.count_cons] <;> omega

lemma rowCount2 (k : ℕ) : (row (4 * k + 6)).count true = 3 * k + 5 := by
  rw [(cycle k).2.2.1.1]
  simp [word2, List.count_append, block_count, List.count_cons] <;> omega

lemma rowCount3 (k : ℕ) : (row (4 * k + 7)).count true = 3 * k + 7 := by
  rw [(cycle k).2.2.2.1]
  simp [word3, List.count_append, block_count, List.count_cons] <;> omega

lemma values (k : ℕ) :
    ((a (4 * k + 4) : ℚ) = 13 + 18 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2) ∧
    ((a (4 * k + 5) : ℚ) = 18 + 21 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2) ∧
    ((a (4 * k + 6) : ℚ) = 23 + 24 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2) ∧
    ((a (4 * k + 7) : ℚ) = 30 + 27 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2) := by
  induction k with
  | zero => norm_num [show a 4 = 13 by rfl, show a 5 = 18 by rfl, show a 6 = 23 by rfl, show a 7 = 30 by rfl]
  | succ k ih =>
    have h0 : (a (4 * (k+1) + 4) : ℚ) = 13 + 18 * ((k+1 : ℕ) : ℚ) + 6 * ((k+1 : ℕ) : ℚ) ^ 2 := by
      have hs : 4 * (k+1) + 4 = (4 * k + 7) + 1 := by omega
      rw [hs, a, ← hs, rowCount0]
      push_cast
      rw [ih.2.2.2]
      push_cast
      simp only [pow_succ]
      ring
    have h1 : (a (4 * (k+1) + 5) : ℚ) = 18 + 21 * ((k+1 : ℕ) : ℚ) + 6 * ((k+1 : ℕ) : ℚ) ^ 2 := by
      have hs : 4 * (k+1) + 5 = (4 * (k+1) + 4) + 1 := by omega
      rw [hs, a, ← hs, rowCount1]
      push_cast
      rw [h0]
      push_cast
      simp only [pow_succ]
      ring
    have h2 : (a (4 * (k+1) + 6) : ℚ) = 23 + 24 * ((k+1 : ℕ) : ℚ) + 6 * ((k+1 : ℕ) : ℚ) ^ 2 := by
      have hs : 4 * (k+1) + 6 = (4 * (k+1) + 5) + 1 := by omega
      rw [hs, a, ← hs, rowCount2]
      push_cast
      rw [h1]
      push_cast
      simp only [pow_succ]
      ring
    have h3 : (a (4 * (k+1) + 7) : ℚ) = 30 + 27 * ((k+1 : ℕ) : ℚ) + 6 * ((k+1 : ℕ) : ℚ) ^ 2 := by
      have hs : 4 * (k+1) + 7 = (4 * (k+1) + 6) + 1 := by omega
      rw [hs, a, ← hs, rowCount3]
      push_cast
      rw [h2]
      push_cast
      simp only [pow_succ]
      ring
    exact ⟨h0, h1, h2, h3⟩
lemma value0 (k : ℕ) : (a (4 * k + 4) : ℚ) = 13 + 18 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := (values k).1
lemma value1 (k : ℕ) : (a (4 * k + 5) : ℚ) = 18 + 21 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := (values k).2.1
lemma value2 (k : ℕ) : (a (4 * k + 6) : ℚ) = 23 + 24 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := (values k).2.2.1
lemma value3 (k : ℕ) : (a (4 * k + 7) : ℚ) = 30 + 27 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := (values k).2.2.2

lemma initial0 : a 0 = 1 := by rfl
lemma initial1 : a 1 = 3 := by rfl
lemma initial2 : a 2 = 5 := by rfl
lemma initial3 : a 3 = 9 := by rfl
lemma initial4 : a 4 = 13 := by rfl
lemma initial5 : a 5 = 18 := by rfl
lemma initial6 : a 6 = 23 := by rfl
lemma initial7 : a 7 = 30 := by rfl
lemma initial8 : a 8 = 37 := by rfl
lemma initial9 : a 9 = 45 := by rfl
lemma initial10 : a 10 = 53 := by rfl
lemma initial11 : a 11 = 63 := by rfl

lemma claim1 : ∀ n : ℕ, (a n : ℂ) = 1 / 16 * (6 * (n : ℂ) ^ 2 + 24 * (n : ℂ) - 3 * (-1) ^ n + 2 * (-Complex.I) ^ n + 2 * Complex.I ^ n + 15) := by
  intro n
  by_cases small : n < 4
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3] at * <;> ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_four, Complex.I_pow_three] <;> ring
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 4 ∨ n = 4 * k + 5 ∨ n = 4 * k + 6 ∨ n = 4 * k + 7 := by
    exact ⟨(n - 4) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = 13 + 18 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 4 by omega]
      exact value0 k
    have vc0 : (a n : ℂ) = 13 + 18 * ((k : ℕ) : ℂ) + 6 * ((k : ℕ) : ℂ) ^ 2 := by exact_mod_cast v0
    have imaginary1 : Complex.I ^ n = Complex.I ^ 0 := by
      rw [Complex.I_pow_eq_pow_mod n, show n % 4 = 0 by omega]
    have imaginary2 : (-Complex.I) ^ n = (-Complex.I) ^ 0 := by
      rw [← Complex.I_pow_three, ← pow_mul, ← pow_mul, Complex.I_pow_eq_pow_mod (3*n), Complex.I_pow_eq_pow_mod (3*0)]
      congr 1 <;> omega
    have power1 : (-1 : ℂ) ^ n = (1 : ℂ) ^ k * (-1 : ℂ) ^ 4 := by
      rw [show n = 4 * k + 4 by omega, pow_add, pow_mul]
      norm_num
    simp only [vc0, imaginary1, imaginary2, power1]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_four, Complex.I_pow_three] <;> ring
  · have v0 : (a n : ℚ) = 18 + 21 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 5 by omega]
      exact value1 k
    have vc0 : (a n : ℂ) = 18 + 21 * ((k : ℕ) : ℂ) + 6 * ((k : ℕ) : ℂ) ^ 2 := by exact_mod_cast v0
    have imaginary1 : Complex.I ^ n = Complex.I ^ 1 := by
      rw [Complex.I_pow_eq_pow_mod n, show n % 4 = 1 by omega]
    have imaginary2 : (-Complex.I) ^ n = (-Complex.I) ^ 1 := by
      rw [← Complex.I_pow_three, ← pow_mul, ← pow_mul, Complex.I_pow_eq_pow_mod (3*n), Complex.I_pow_eq_pow_mod (3*1)]
      congr 1 <;> omega
    have power1 : (-1 : ℂ) ^ n = (1 : ℂ) ^ k * (-1 : ℂ) ^ 5 := by
      rw [show n = 4 * k + 5 by omega, pow_add, pow_mul]
      norm_num
    simp only [vc0, imaginary1, imaginary2, power1]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_four, Complex.I_pow_three] <;> ring
  · have v0 : (a n : ℚ) = 23 + 24 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 6 by omega]
      exact value2 k
    have vc0 : (a n : ℂ) = 23 + 24 * ((k : ℕ) : ℂ) + 6 * ((k : ℕ) : ℂ) ^ 2 := by exact_mod_cast v0
    have imaginary1 : Complex.I ^ n = Complex.I ^ 2 := by
      rw [Complex.I_pow_eq_pow_mod n, show n % 4 = 2 by omega]
    have imaginary2 : (-Complex.I) ^ n = (-Complex.I) ^ 2 := by
      rw [← Complex.I_pow_three, ← pow_mul, ← pow_mul, Complex.I_pow_eq_pow_mod (3*n), Complex.I_pow_eq_pow_mod (3*2)]
      congr 1 <;> omega
    have power1 : (-1 : ℂ) ^ n = (1 : ℂ) ^ k * (-1 : ℂ) ^ 6 := by
      rw [show n = 4 * k + 6 by omega, pow_add, pow_mul]
      norm_num
    simp only [vc0, imaginary1, imaginary2, power1]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_four, Complex.I_pow_three] <;> ring
  · have v0 : (a n : ℚ) = 30 + 27 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 7 by omega]
      exact value3 k
    have vc0 : (a n : ℂ) = 30 + 27 * ((k : ℕ) : ℂ) + 6 * ((k : ℕ) : ℂ) ^ 2 := by exact_mod_cast v0
    have imaginary1 : Complex.I ^ n = Complex.I ^ 3 := by
      rw [Complex.I_pow_eq_pow_mod n, show n % 4 = 3 by omega]
    have imaginary2 : (-Complex.I) ^ n = (-Complex.I) ^ 3 := by
      rw [← Complex.I_pow_three, ← pow_mul, ← pow_mul, Complex.I_pow_eq_pow_mod (3*n), Complex.I_pow_eq_pow_mod (3*3)]
      congr 1 <;> omega
    have power1 : (-1 : ℂ) ^ n = (1 : ℂ) ^ k * (-1 : ℂ) ^ 7 := by
      rw [show n = 4 * k + 7 by omega, pow_add, pow_mul]
      norm_num
    simp only [vc0, imaginary1, imaginary2, power1]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_four, Complex.I_pow_three] <;> ring

lemma claim2Tail : ∀ n : ℕ, 5 < n → (a n : ℚ) = -(-1 * (a (n - 6) : ℚ) + -1 * (a (n - 4) : ℚ) + 2 * (a (n - 5) : ℚ) + 1 * (a (n - 2) : ℚ) + -2 * (a (n - 1) : ℚ)) := by
  intro n hn
  by_cases small : n < 12
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10, initial11] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 12 ∨ n = 4 * k + 13 ∨ n = 4 * k + 14 ∨ n = 4 * k + 15 := by
    exact ⟨(n - 12) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = 13 + 18 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v1 : (a (n - 1) : ℚ) = 30 + 27 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 1 = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    have v2 : (a (n - 2) : ℚ) = 23 + 24 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 2 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    have v3 : (a (n - 5) : ℚ) = 30 + 27 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n - 5 = 4 * k + 7 by omega]
      exact value3 k
    have v4 : (a (n - 6) : ℚ) = 23 + 24 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n - 6 = 4 * k + 6 by omega]
      exact value2 k
    have v5 : (a (n - 4) : ℚ) = 13 + 18 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 4 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3, v4, v5]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring
  · have v0 : (a n : ℚ) = 18 + 21 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v1 : (a (n - 1) : ℚ) = 13 + 18 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 1 = 4 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v2 : (a (n - 2) : ℚ) = 30 + 27 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 2 = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    have v3 : (a (n - 5) : ℚ) = 13 + 18 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 5 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v4 : (a (n - 6) : ℚ) = 30 + 27 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n - 6 = 4 * k + 7 by omega]
      exact value3 k
    have v5 : (a (n - 4) : ℚ) = 18 + 21 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 4 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3, v4, v5]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring
  · have v0 : (a n : ℚ) = 23 + 24 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * (k + 2) + 6 by omega]
      exact value2 (k + 2)
    have v1 : (a (n - 1) : ℚ) = 18 + 21 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 1 = 4 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v2 : (a (n - 2) : ℚ) = 13 + 18 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 2 = 4 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v3 : (a (n - 5) : ℚ) = 18 + 21 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 5 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    have v4 : (a (n - 6) : ℚ) = 13 + 18 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 6 = 4 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    have v5 : (a (n - 4) : ℚ) = 23 + 24 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 4 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    simp only [v0, v1, v2, v3, v4, v5]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring
  · have v0 : (a n : ℚ) = 30 + 27 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * (k + 2) + 7 by omega]
      exact value3 (k + 2)
    have v1 : (a (n - 1) : ℚ) = 23 + 24 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 1 = 4 * (k + 2) + 6 by omega]
      exact value2 (k + 2)
    have v2 : (a (n - 2) : ℚ) = 18 + 21 * ((k + 2 : ℕ) : ℚ) + 6 * ((k + 2 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 2 = 4 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v3 : (a (n - 5) : ℚ) = 23 + 24 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 5 = 4 * (k + 1) + 6 by omega]
      exact value2 (k + 1)
    have v4 : (a (n - 6) : ℚ) = 18 + 21 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 6 = 4 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    have v5 : (a (n - 4) : ℚ) = 30 + 27 * ((k + 1 : ℕ) : ℚ) + 6 * ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [show n - 4 = 4 * (k + 1) + 7 by omega]
      exact value3 (k + 1)
    simp only [v0, v1, v2, v3, v4, v5]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring

open PowerSeries in
lemma claim2 : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2)) = 1 + X + 2 * X ^ 3 - X ^ 4 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  have hd : s * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2)) = PowerSeries.C (1 : ℚ) * (s * X ^ 0) + PowerSeries.C (-2 : ℚ) * (s * X ^ 1) + PowerSeries.C (1 : ℚ) * (s * X ^ 2) + PowerSeries.C (-1 : ℚ) * (s * X ^ 4) + PowerSeries.C (2 : ℚ) * (s * X ^ 5) + PowerSeries.C (-1 : ℚ) * (s * X ^ 6) := by norm_num [map_ofNat] <;> ring
  have hn : 1 + X + 2 * X ^ 3 - X ^ 4 = PowerSeries.C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ) + PowerSeries.C (1 : ℚ) * (X ^ 1 : PowerSeries ℚ) + PowerSeries.C (2 : ℚ) * (X ^ 3 : PowerSeries ℚ) + PowerSeries.C (-1 : ℚ) * (X ^ 4 : PowerSeries ℚ) := by norm_num [map_ofNat] <;> ring
  rw [hd, hn]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_X_pow, coeff_mul_X_pow', s, coeff_mk]
  by_cases h : n ≤ 5
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5]
  · have hr := claim2Tail n (by omega)
    simp only [if_pos (show 6 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 1 ≤ n by omega), if_pos (show 0 ≤ n by omega), if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), Nat.sub_zero]
    linarith

lemma bracketLower : ∀ n : ℕ, 8 * (a n : ℚ) < 3 * ((n : ℚ) + 2) ^ 2 := by
  intro n
  by_cases small : n < 4
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 4 ∨ n = 4 * k + 5 ∨ n = 4 * k + 6 ∨ n = 4 * k + 7 := by
    exact ⟨(n - 4) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = 13 + 18 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 4 by omega]
      exact value0 k
    simp only [v0]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num <;> linarith only []
  · have v0 : (a n : ℚ) = 18 + 21 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 5 by omega]
      exact value1 k
    simp only [v0]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num <;> linarith only []
  · have v0 : (a n : ℚ) = 23 + 24 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 6 by omega]
      exact value2 k
    simp only [v0]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num <;> linarith only []
  · have v0 : (a n : ℚ) = 30 + 27 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 7 by omega]
      exact value3 k
    simp only [v0]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num <;> linarith only []

lemma bracketUpper : ∀ n : ℕ, 3 * ((n : ℚ) + 2) ^ 2 ≤ 8 * ((a n : ℚ) + 1) := by
  intro n
  by_cases small : n < 4
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 4 ∨ n = 4 * k + 5 ∨ n = 4 * k + 6 ∨ n = 4 * k + 7 := by
    exact ⟨(n - 4) / 4, by omega⟩
  rcases hk with hk | hk | hk | hk
  · have v0 : (a n : ℚ) = 13 + 18 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 4 by omega]
      exact value0 k
    simp only [v0]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num <;> linarith only []
  · have v0 : (a n : ℚ) = 18 + 21 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 5 by omega]
      exact value1 k
    simp only [v0]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num <;> linarith only []
  · have v0 : (a n : ℚ) = 23 + 24 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 6 by omega]
      exact value2 k
    simp only [v0]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num <;> linarith only []
  · have v0 : (a n : ℚ) = 30 + 27 * ((k : ℕ) : ℚ) + 6 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show n = 4 * k + 7 by omega]
      exact value3 k
    simp only [v0]
    try rw [hk]
    all_goals
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [one_pow]
      all_goals ring_nf <;> norm_num <;> linarith only []

lemma bracket (n : ℕ) : 8 * a n < 3 * (n+2)^2 ∧ 3*(n+2)^2 ≤ 8*(a n+1) := by
  exact ⟨by exact_mod_cast bracketLower n, by exact_mod_cast bracketUpper n⟩

lemma floorJump (k : ℕ) :
    ⌊Real.sqrt (8 * ((k : ℝ)+1) / 3)⌋ ≠ ⌊Real.sqrt (8 * (k : ℝ) / 3)⌋ ↔
    ∃ m : ℕ, 8*k < 3*m^2 ∧ 3*m^2 ≤ 8*(k+1) := by
  let x := Real.sqrt (8*(k : ℝ)/3)
  let y := Real.sqrt (8*((k : ℝ)+1)/3)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hx2 : x^2 = 8*(k : ℝ)/3 := Real.sq_sqrt (by positivity)
  have hy2 : y^2 = 8*((k : ℝ)+1)/3 := Real.sq_sqrt (by positivity)
  have hxy : x ≤ y := Real.sqrt_le_sqrt (by linarith)
  change ⌊y⌋ ≠ ⌊x⌋ ↔ _
  constructor
  · intro hn
    have hlt : ⌊x⌋ < ⌊y⌋ := lt_of_le_of_ne (Int.floor_mono hxy) (Ne.symm hn)
    let m := (⌊x⌋+1).toNat
    have h0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
    have hm : (m : ℤ) = ⌊x⌋+1 := Int.toNat_of_nonneg (by omega)
    have hl : x < (m : ℝ) := by
      have eq : (m : ℝ) = (⌊x⌋ : ℝ)+1 := by exact_mod_cast hm
      rw [eq]
      exact Int.lt_floor_add_one _
    have hr : (m : ℝ) ≤ y := by
      apply le_trans _ (Int.floor_le y)
      exact_mod_cast (show (m : ℤ) ≤ ⌊y⌋ by omega)
    have hml : 0 ≤ (m : ℝ) := by positivity
    have f := (sq_lt_sq₀ hx hml).mpr hl
    have g := (sq_le_sq₀ hml hy).mpr hr
    refine ⟨m, ?_, ?_⟩
    · exact_mod_cast (show 8*(k : ℝ) < 3*(m : ℝ)^2 by linarith)
    · exact_mod_cast (show 3*(m : ℝ)^2 ≤ 8*((k : ℝ)+1) by linarith)
  · rintro ⟨m, hl, hr⟩
    have hml : 0 ≤ (m : ℝ) := by positivity
    have hl' : 8*(k : ℝ) < 3*(m : ℝ)^2 := by exact_mod_cast hl
    have hr' : 3*(m : ℝ)^2 ≤ 8*((k : ℝ)+1) := by exact_mod_cast hr
    have hx' : x < (m : ℝ) := (sq_lt_sq₀ hx hml).mp (by linarith)
    have hy' : (m : ℝ) ≤ y := (sq_le_sq₀ hml hy).mp (by linarith)
    have u : ⌊x⌋ < (m : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hx')
    have v : (m : ℤ) ≤ ⌊y⌋ := Int.le_floor.mpr (by exact_mod_cast hy')
    omega

lemma claim3 : ∀ k : ℕ, (∃ n : ℕ, a n = k) ↔ 0 < k ∧ ⌊Real.sqrt (8 * ((k : ℝ) + 1) / 3)⌋ ≠ ⌊Real.sqrt (8 * (k : ℝ) / 3)⌋ := by
  intro k
  rw [floorJump]
  constructor
  · rintro ⟨n, rfl⟩
    have h := bracket n
    have hn : 4 ≤ (n+2)^2 := Nat.pow_le_pow_left (by omega : 2 ≤ n+2) 2
    exact ⟨by omega, n+2, h⟩
  · rintro ⟨hk, m, h₁, h₂⟩
    have hm : 2 ≤ m := by
      by_contra! h
      interval_cases m <;> omega
    have h := bracket (m-2)
    rw [Nat.sub_add_cancel hm] at h
    exact ⟨m-2, by omega⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a265429.main := by
  exact ⟨claim1, claim2, claim3⟩
