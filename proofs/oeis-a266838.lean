import OMAStatements.S_oeis_a266838

open OMA.S_oeis_a266838

def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, tail => tail
  | k + 1, tail => w ++ blocks w k tail

lemma blocks_append (w : List Bool) (k : ℕ) (u v : List Bool) :
    blocks w k u ++ v = blocks w k (u ++ v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

def word0 (k : ℕ) : List Bool :=
  blocks [false] k ([false, false, true, false, true, true, true, false, false] ++ blocks [false, false, false] k [])

def word1 (k : ℕ) : List Bool :=
  blocks [true] k ([true, true, true, false, false, false, false, true, false, true, true] ++ blocks [true, true, true] k [])

lemma align1 (k : ℕ) (tail : List Bool) :
    blocks [false] (k + 2) tail =
      [false, false] ++ blocks [false] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false] ++ rest) ih

lemma align2 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false] (k + 2) tail =
      [false, false, false, false] ++ blocks [false, false, false] k ([false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false] ++ rest) ih

lemma align3 (k : ℕ) (tail : List Bool) :
    blocks [true] (k + 2) tail =
      [true, true] ++ blocks [true] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true] ++ rest) ih

lemma align4 (k : ℕ) (tail : List Bool) :
    blocks [true, true, true] (k + 2) tail =
      [true, true] ++ blocks [true, true, true] k ([true, true, true, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true, true] ++ rest) ih

lemma scanBlock1 (k : ℕ) (tail : List Bool) :
    scan false false (blocks [false] k tail) =
      blocks [true] k (scan false false tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true] ++ rest) ih

lemma scanBlock2 (k : ℕ) (tail : List Bool) :
    scan false false (blocks [false, false, false] k tail) =
      blocks [true, true, true] k (scan false false tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true, true, true] ++ rest) ih

lemma align5 (k : ℕ) (tail : List Bool) :
    blocks [false] (k + 3) tail =
      [false, false] ++ blocks [false] k ([false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false] ++ rest) ih

lemma align6 (k : ℕ) (tail : List Bool) :
    blocks [false, false, false] (k + 3) tail =
      [false, false, false] ++ blocks [false, false, false] k ([false, false, false, false, false, false] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [false, false, false] ++ rest) ih

lemma scanBlock3 (k : ℕ) (tail : List Bool) :
    scan true true (blocks [true] k tail) =
      blocks [false] k (scan true true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false] ++ rest) ih

lemma scanBlock4 (k : ℕ) (tail : List Bool) :
    scan true true (blocks [true, true, true] k tail) =
      blocks [false, false, false] k (scan true true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [false, false, false] ++ rest) ih

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
      change scan false false (blocks [false] (k + 2) ([false, false, true, false, true, true, true, false, false] ++ blocks [false, false, false] (k + 2) ([false, false]))) = blocks [true] (k + 2) ([true, true, true, false, false, false, false, true, false, true, true] ++ blocks [true, true, true] (k + 2) [])
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
    cases k with
    | zero => rfl
    | succ k =>
      simp only [word1, word0, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
      change scan true true (blocks [true] (k + 2) ([true, true, true, false, false, false, false, true, false, true, true] ++ blocks [true, true, true] (k + 2) ([true, true]))) = blocks [false] (k + 3) ([false, false, true, false, true, true, true, false, false] ++ blocks [false, false, false] (k + 3) [])
      conv => lhs; rw [align3]
      conv => lhs; rw [align4]
      conv => rhs; rw [align5]
      conv => rhs; rw [align6]
      simp only [List.cons_append, List.nil_append, scan, scanBlock3, scanBlock4]
      <;> rfl

lemma cycle (k : ℕ) :
    (row (2 * k + 4) = word0 k ∧ background (2 * k + 4) = false) ∧
    (row (2 * k + 5) = word1 k ∧ background (2 * k + 5) = true) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h0 : row (2 * (k + 1) + 4) = word0 (k+1) ∧ background (2 * (k + 1) + 4) = false := by
      rw [show 2 * (k + 1) + 4 = (2 * k + 5) + 1 by omega]
      exact ⟨by rw [row, ih.2.1, ih.2.2]; exact phase1 k, by rw [background, ih.2.2]; rfl⟩
    have h1 : row (2 * (k + 1) + 5) = word1 (k+1) ∧ background (2 * (k + 1) + 5) = true := by
      rw [show 2 * (k + 1) + 5 = (2 * (k + 1) + 4) + 1 by omega]
      exact ⟨by rw [row, h0.1, h0.2]; exact phase0 (k + 1), by rw [background, h0.2]; rfl⟩
    exact ⟨h0, h1⟩

def magnitude (w : List Bool) : ℚ := (10 : ℚ) ^ w.length

def encode (w : List Bool) : ℚ := (Nat.ofDigits 10 (w.map Bool.toNat).reverse : ℕ)

lemma magnitude_append (u v : List Bool) : magnitude (u ++ v) = magnitude u * magnitude v := by
  simp [magnitude, pow_add]

lemma encode_append (u v : List Bool) : encode (u ++ v) = encode u * magnitude v + encode v := by
  simp [encode, magnitude, Nat.ofDigits_append]
  ring

lemma run0 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [false] k tail) = (10 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [false] k tail) =
      0 * ((10 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [false] = 10 := by decide
    have he : encode [false] = 0 := by decide
    rw [hm, he]
    constructor <;> ring

lemma run000 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [false, false, false] k tail) = (1000 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [false, false, false] k tail) =
      0 * ((1000 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [false, false, false] = 1000 := by decide
    have he : encode [false, false, false] = 0 := by decide
    rw [hm, he]
    constructor <;> ring

lemma run1 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [true] k tail) = (10 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [true] k tail) =
      (1 / 9) * ((10 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [true] = 10 := by decide
    have he : encode [true] = 1 := by decide
    rw [hm, he]
    constructor <;> ring

lemma run111 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [true, true, true] k tail) = (1000 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [true, true, true] k tail) =
      (1 / 9) * ((1000 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [true, true, true] = 1000 := by decide
    have he : encode [true, true, true] = 111 := by decide
    rw [hm, he]
    constructor <;> ring

lemma value0 (k : ℕ) : (a (2 * k + 4) : ℚ) = 1011100 * (1000 : ℚ) ^ k := by
  change encode (row (2 * k + 4)) = _
  rw [(cycle k).1.1, word0]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [false, false, true, false, true, true, true, false, false] = 1011100 := by decide
  have m1 : magnitude [false, false, true, false, true, true, true, false, false] = 1000000000 := by decide
  have z0 := fun tail => (run0 k tail).1
  have y0 := fun tail => (run0 k tail).2
  have z1 := fun tail => (run000 k tail).1
  have y1 := fun tail => (run000 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0, z1, y1]
  have p10 : (10 : ℚ) ^ k = (2 ^ k : ℚ) ^ 1 * (5 ^ k : ℚ) ^ 1 := by
    calc _ = (((2 : ℚ) ^ 1) * (5 ^ 1)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  have p1000 : (1000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 3 * (5 ^ k : ℚ) ^ 3 := by
    calc _ = (((2 : ℚ) ^ 3) * (5 ^ 3)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
    calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p10, p1000, p10000]
  all_goals ring

lemma value1 (k : ℕ) : (a (2 * k + 5) : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ k + (100000000000 / 9) * (10000 : ℚ) ^ k := by
  change encode (row (2 * k + 5)) = _
  rw [(cycle k).2.1, word1]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [true, true, true, false, false, false, false, true, false, true, true] = 11100001011 := by decide
  have m1 : magnitude [true, true, true, false, false, false, false, true, false, true, true] = 100000000000 := by decide
  have z0 := fun tail => (run1 k tail).1
  have y0 := fun tail => (run1 k tail).2
  have z1 := fun tail => (run111 k tail).1
  have y1 := fun tail => (run111 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0, z1, y1]
  have p10 : (10 : ℚ) ^ k = (2 ^ k : ℚ) ^ 1 * (5 ^ k : ℚ) ^ 1 := by
    calc _ = (((2 : ℚ) ^ 1) * (5 ^ 1)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  have p1000 : (1000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 3 * (5 ^ k : ℚ) ^ 3 := by
    calc _ = (((2 : ℚ) ^ 3) * (5 ^ 3)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
    calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p10, p1000, p10000]
  all_goals ring


lemma initial0 : a 0 = 1 := by rfl
lemma initial1 : a 1 = 100 := by rfl
lemma initial2 : a 2 = 1010 := by rfl
lemma initial3 : a 3 = 1100001 := by rfl
lemma initial4 : a 4 = 1011100 := by rfl
lemma initial5 : a 5 = 11100001011 := by rfl
lemma initial6 : a 6 = 1011100000 := by rfl
lemma initial7 : a 7 = 111100001011111 := by rfl
lemma initial8 : a 8 = 1011100000000 := by rfl
lemma initial9 : a 9 = 1111100001011111111 := by rfl

lemma claim1 : ∀ n : ℕ, 9 < n → (a n : ℤ) = 11001 * (a (n - 2) : ℤ) - 10011000 * (a (n - 4) : ℤ) + 10000000 * (a (n - 6) : ℤ) := by
  intro n hn
  suffices hq : (a n : ℚ) = 11001 * (a (n - 2) : ℚ) - 10011000 * (a (n - 4) : ℚ) + 10000000 * (a (n - 6) : ℚ) by exact_mod_cast hq
  by_cases small : n < 10
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 10 ∨ n = 2 * k + 11 := by
    exact ⟨(n - 10) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 1011100 * (1000 : ℚ) ^ (k + 3) := by
      rw [show n = 2 * (k + 3) + 4 by omega]
      exact value0 (k + 3)
    have v1 : (a (n - 6) : ℚ) = 1011100 * (1000 : ℚ) ^ k := by
      rw [show n - 6 = 2 * k + 4 by omega]
      exact value0 k
    have v2 : (a (n - 2) : ℚ) = 1011100 * (1000 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 2 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v3 : (a (n - 4) : ℚ) = 1011100 * (1000 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 2 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p1000 : (1000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 3 * (5 ^ k : ℚ) ^ 3 := by
        calc _ = (((2 : ℚ) ^ 3) * (5 ^ 3)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p1000, p10000]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ (k + 3) + (100000000000 / 9) * (10000 : ℚ) ^ (k + 3) := by
      rw [show n = 2 * (k + 3) + 5 by omega]
      exact value1 (k + 3)
    have v1 : (a (n - 6) : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ k + (100000000000 / 9) * (10000 : ℚ) ^ k := by
      rw [show n - 6 = 2 * k + 5 by omega]
      exact value1 k
    have v2 : (a (n - 2) : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ (k + 2) + (100000000000 / 9) * (10000 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 2 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v3 : (a (n - 4) : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ (k + 1) + (100000000000 / 9) * (10000 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 2 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p1000 : (1000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 3 * (5 ^ k : ℚ) ^ 3 := by
        calc _ = (((2 : ℚ) ^ 3) * (5 ^ 3)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p1000, p10000]
      all_goals ring

lemma claim2Tail : ∀ n : ℕ, 9 < n → (a n : ℚ) = -(-10000000 * (a (n - 6) : ℚ) + 10011000 * (a (n - 4) : ℚ) + -11001 * (a (n - 2) : ℚ)) := by
  intro n hn
  by_cases small : n < 10
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 10 ∨ n = 2 * k + 11 := by
    exact ⟨(n - 10) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 1011100 * (1000 : ℚ) ^ (k + 3) := by
      rw [show n = 2 * (k + 3) + 4 by omega]
      exact value0 (k + 3)
    have v1 : (a (n - 2) : ℚ) = 1011100 * (1000 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 2 * (k + 2) + 4 by omega]
      exact value0 (k + 2)
    have v2 : (a (n - 6) : ℚ) = 1011100 * (1000 : ℚ) ^ k := by
      rw [show n - 6 = 2 * k + 4 by omega]
      exact value0 k
    have v3 : (a (n - 4) : ℚ) = 1011100 * (1000 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 2 * (k + 1) + 4 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p1000 : (1000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 3 * (5 ^ k : ℚ) ^ 3 := by
        calc _ = (((2 : ℚ) ^ 3) * (5 ^ 3)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p1000, p10000]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ (k + 3) + (100000000000 / 9) * (10000 : ℚ) ^ (k + 3) := by
      rw [show n = 2 * (k + 3) + 5 by omega]
      exact value1 (k + 3)
    have v1 : (a (n - 2) : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ (k + 2) + (100000000000 / 9) * (10000 : ℚ) ^ (k + 2) := by
      rw [show n - 2 = 2 * (k + 2) + 5 by omega]
      exact value1 (k + 2)
    have v2 : (a (n - 6) : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ k + (100000000000 / 9) * (10000 : ℚ) ^ k := by
      rw [show n - 6 = 2 * k + 5 by omega]
      exact value1 k
    have v3 : (a (n - 4) : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ (k + 1) + (100000000000 / 9) * (10000 : ℚ) ^ (k + 1) := by
      rw [show n - 4 = 2 * (k + 1) + 5 by omega]
      exact value1 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p1000 : (1000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 3 * (5 ^ k : ℚ) ^ 3 := by
        calc _ = (((2 : ℚ) ^ 3) * (5 ^ 3)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p1000, p10000]
      all_goals ring

open PowerSeries in
lemma claim2 : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) = 1 + 100 * X - 9991 * X ^ 2 - 99 * X ^ 3 - 88910 * X ^ 4 - 9990 * X ^ 5 - 10901100 * X ^ 6 - 99900 * X ^ 7 + 11000000 * X ^ 8 - 1000000 * X ^ 9 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  have hd : s * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) = PowerSeries.C (1 : ℚ) * (s * X ^ 0) + PowerSeries.C (-11001 : ℚ) * (s * X ^ 2) + PowerSeries.C (10011000 : ℚ) * (s * X ^ 4) + PowerSeries.C (-10000000 : ℚ) * (s * X ^ 6) := by norm_num [map_ofNat] <;> ring
  have hn : 1 + 100 * X - 9991 * X ^ 2 - 99 * X ^ 3 - 88910 * X ^ 4 - 9990 * X ^ 5 - 10901100 * X ^ 6 - 99900 * X ^ 7 + 11000000 * X ^ 8 - 1000000 * X ^ 9 = PowerSeries.C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ) + PowerSeries.C (100 : ℚ) * (X ^ 1 : PowerSeries ℚ) + PowerSeries.C (-9991 : ℚ) * (X ^ 2 : PowerSeries ℚ) + PowerSeries.C (-99 : ℚ) * (X ^ 3 : PowerSeries ℚ) + PowerSeries.C (-88910 : ℚ) * (X ^ 4 : PowerSeries ℚ) + PowerSeries.C (-9990 : ℚ) * (X ^ 5 : PowerSeries ℚ) + PowerSeries.C (-10901100 : ℚ) * (X ^ 6 : PowerSeries ℚ) + PowerSeries.C (-99900 : ℚ) * (X ^ 7 : PowerSeries ℚ) + PowerSeries.C (11000000 : ℚ) * (X ^ 8 : PowerSeries ℚ) + PowerSeries.C (-1000000 : ℚ) * (X ^ 9 : PowerSeries ℚ) := by norm_num [map_ofNat] <;> ring
  rw [hd, hn]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_X_pow, coeff_mul_X_pow', s, coeff_mk]
  by_cases h : n ≤ 9
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9]
  · have hr := claim2Tail n (by omega)
    simp only [if_pos (show 6 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 0 ≤ n by omega), if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega), if_neg (show n ≠ 9 by omega), Nat.sub_zero]
    linarith

lemma claim3 : ∀ n : ℕ, 3 < n → Odd n → (a n : ℚ) = (10 * 100 ^ n - 999909 * 1000 ^ (⌊((n : ℚ) / 2 : ℚ)⌋).toNat / 10000 - 1) / 9 := by
  intro n hn hpar
  by_cases small : n < 4
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 4 ∨ n = 2 * k + 5 := by
    exact ⟨(n - 4) / 2, by omega⟩
  rcases hk with hk | hk
  · rw [Nat.odd_iff] at hpar
    omega
  · have v0 : (a n : ℚ) = (-1 / 9) + (-11110100) * (1000 : ℚ) ^ k + (100000000000 / 9) * (10000 : ℚ) ^ k := by
      rw [show n = 2 * k + 5 by omega]
      exact value1 k
    have power1 : (100 : ℚ) ^ n = (10000 : ℚ) ^ k * (100 : ℚ) ^ 5 := by
      rw [show n = 2 * k + 5 by omega, pow_add, pow_mul]
      norm_num
    have power2 : (1000 : ℚ) ^ ((⌊((n : ℚ) / 2 : ℚ)⌋).toNat) = (1000 : ℚ) ^ k * (1000 : ℚ) ^ 2 := by
      have hf : ⌊((n : ℚ) / 2)⌋ = (n : ℤ) / 2 := Rat.floor_natCast_div_natCast n 2
      rw [show (⌊((n : ℚ) / 2 : ℚ)⌋).toNat = 1 * k + 2 by rw [hf]; omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1, power2]
    try rw [hk]
    all_goals
      have p1000 : (1000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 3 * (5 ^ k : ℚ) ^ 3 := by
        calc _ = (((2 : ℚ) ^ 3) * (5 ^ 3)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p1000, p10000]
      all_goals ring

lemma claim4 : ∀ n : ℕ, 3 < n → Even n → (a n : ℚ) = 10111 * 1000 ^ (n / 2) / 10000 := by
  intro n hn hpar
  by_cases small : n < 4
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 4 ∨ n = 2 * k + 5 := by
    exact ⟨(n - 4) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = 1011100 * (1000 : ℚ) ^ k := by
      rw [show n = 2 * k + 4 by omega]
      exact value0 k
    have power1 : (1000 : ℚ) ^ (n / 2) = (1000 : ℚ) ^ k * (1000 : ℚ) ^ 2 := by
      rw [show n / 2 = 1 * k + 2 by omega, pow_add, pow_mul]
      norm_num
    simp only [v0, power1]
    try rw [hk]
    all_goals
      have p1000 : (1000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 3 * (5 ^ k : ℚ) ^ 3 := by
        calc _ = (((2 : ℚ) ^ 3) * (5 ^ 3)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p10000 : (10000 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 4 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 4)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p1000, p10000]
      all_goals ring
  · rw [Nat.even_iff] at hpar
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a266838.main := by
  exact ⟨claim1, claim2, claim3, claim4⟩
