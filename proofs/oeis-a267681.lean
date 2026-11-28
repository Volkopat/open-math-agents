import OMAStatements.S_oeis_a267681

open OMA.S_oeis_a267681

def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, tail => tail
  | k + 1, tail => w ++ blocks w k tail

lemma blocks_append (w : List Bool) (k : ℕ) (u v : List Bool) :
    blocks w k u ++ v = blocks w k (u ++ v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

def word0 (k : ℕ) : List Bool :=
  blocks [true, true] k ([true, false, true, false, true] ++ blocks [true, true] k [])

def word1 (k : ℕ) : List Bool :=
  blocks [true, true] k ([true, true, false, false, false, true, true] ++ blocks [true, true] k [])

lemma align1 (k : ℕ) (tail : List Bool) :
    blocks [true, true] (k + 2) tail =
      [true, true] ++ blocks [true, true] k ([true, true] ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true] ++ rest) ih

lemma align2 (k : ℕ) (tail : List Bool) :
    blocks [true, true] (k + 2) tail =
      [true, true, true, true] ++ blocks [true, true] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true] ++ rest) ih

lemma scanBlock1 (k : ℕ) (tail : List Bool) :
    scan true true (blocks [true, true] k tail) =
      blocks [true, true] k (scan true true tail) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun rest => [true, true] ++ rest) ih

lemma align3 (k : ℕ) (tail : List Bool) :
    blocks [true, true] (k + 1) tail =
      [true, true] ++ blocks [true, true] k tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun rest => [true, true] ++ rest) ih

lemma phase0 (k : ℕ) :
    scan true true ((word0 k) ++ [true, true]) =
      word1 k := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [word0, word1, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
      change scan true true (blocks [true, true] (k + 2) ([true, false, true, false, true] ++ blocks [true, true] (k + 2) ([true, true]))) = blocks [true, true] (k + 2) ([true, true, false, false, false, true, true] ++ blocks [true, true] (k + 2) [])
      conv => lhs; rw [align1]
      conv => lhs; rw [align2]
      conv => rhs; rw [align1]
      conv => rhs; rw [align1]
      simp only [List.cons_append, List.nil_append, scan, scanBlock1]
      <;> rfl

lemma phase1 (k : ℕ) :
    scan true true ((word1 k) ++ [true, true]) =
      word0 (k + 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [word1, word0, List.append_assoc, blocks_append, List.cons_append, List.nil_append]
    change scan true true (blocks [true, true] (k + 1) ([true, true, false, false, false, true, true] ++ blocks [true, true] (k + 1) ([true, true]))) = blocks [true, true] (k + 2) ([true, false, true, false, true] ++ blocks [true, true] (k + 2) [])
    conv => lhs; rw [align3]
    conv => lhs; rw [align3]
    conv => rhs; rw [align1]
    conv => rhs; rw [align1]
    simp only [List.cons_append, List.nil_append, scan, scanBlock1]
    <;> rfl

lemma cycle (k : ℕ) :
    (row (2 * k + 2) = word0 k ∧ background (2 * k + 2) = true) ∧
    (row (2 * k + 3) = word1 k ∧ background (2 * k + 3) = true) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h0 : row (2 * (k + 1) + 2) = word0 (k+1) ∧ background (2 * (k + 1) + 2) = true := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by omega]
      exact ⟨by rw [row, ih.2.1, ih.2.2]; exact phase1 k, by rw [background, ih.2.2]; rfl⟩
    have h1 : row (2 * (k + 1) + 3) = word1 (k+1) ∧ background (2 * (k + 1) + 3) = true := by
      rw [show 2 * (k + 1) + 3 = (2 * (k + 1) + 2) + 1 by omega]
      exact ⟨by rw [row, h0.1, h0.2]; exact phase0 (k + 1), by rw [background, h0.2]; rfl⟩
    exact ⟨h0, h1⟩

def magnitude (w : List Bool) : ℚ := (2 : ℚ) ^ w.length

def encode (w : List Bool) : ℚ := (Nat.ofDigits 2 (w.map Bool.toNat).reverse : ℕ)

lemma magnitude_append (u v : List Bool) : magnitude (u ++ v) = magnitude u * magnitude v := by
  simp [magnitude, pow_add]

lemma encode_append (u v : List Bool) : encode (u ++ v) = encode u * magnitude v + encode v := by
  simp [encode, magnitude, Nat.ofDigits_append]
  ring

lemma run11 (k : ℕ) (tail : List Bool) :
    magnitude (blocks [true, true] k tail) = (4 : ℚ) ^ k * magnitude tail ∧
    encode (blocks [true, true] k tail) =
      1 * ((4 : ℚ) ^ k - 1) * magnitude tail + encode tail := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, magnitude_append, encode_append, ih.1, ih.2, pow_succ]
    have hm : magnitude [true, true] = 4 := by decide
    have he : encode [true, true] = 3 := by decide
    rw [hm, he]
    constructor <;> ring

lemma value0 (k : ℕ) : (a (2 * k + 2) : ℚ) = (-1) + (-10) * (4 : ℚ) ^ k + 32 * (16 : ℚ) ^ k := by
  change encode (row (2 * k + 2)) = _
  rw [(cycle k).1.1, word0]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [true, false, true, false, true] = 21 := by decide
  have m1 : magnitude [true, false, true, false, true] = 32 := by decide
  have z0 := fun tail => (run11 k tail).1
  have y0 := fun tail => (run11 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0]
  have p4 : (4 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 0 := by
    calc _ = (((2 : ℚ) ^ 2) * (5 ^ 0)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
    calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p4, p16]
  all_goals ring

lemma value1 (k : ℕ) : (a (2 * k + 3) : ℚ) = (-1) + (-28) * (4 : ℚ) ^ k + 128 * (16 : ℚ) ^ k := by
  change encode (row (2 * k + 3)) = _
  rw [(cycle k).2.1, word1]
  have e0 : encode [] = 0 := by decide
  have m0 : magnitude [] = 1 := by decide
  have e1 : encode [true, true, false, false, false, true, true] = 99 := by decide
  have m1 : magnitude [true, true, false, false, false, true, true] = 128 := by decide
  have z0 := fun tail => (run11 k tail).1
  have y0 := fun tail => (run11 k tail).2
  simp only [encode_append, magnitude_append, e0, m0, e1, m1, z0, y0]
  have p4 : (4 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 0 := by
    calc _ = (((2 : ℚ) ^ 2) * (5 ^ 0)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
    calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
         _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
  push_cast
  norm_num [pow_succ, pow_add, pow_mul]
  all_goals try simp only [p4, p16]
  all_goals ring


lemma initial0 : a 0 = 1 := by rfl
lemma initial1 : a 1 = 0 := by rfl
lemma initial2 : a 2 = 21 := by rfl
lemma initial3 : a 3 = 99 := by rfl
lemma initial4 : a 4 = 471 := by rfl
lemma initial5 : a 5 = 1935 := by rfl

lemma claim1 : ∀ n : ℕ, 4 < n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 20 * (a (n - 3) : ℤ) + 16 * (a (n - 4) : ℤ) := by
  intro n hn
  suffices hq : (a n : ℚ) = 5 * (a (n - 1) : ℚ) - 20 * (a (n - 3) : ℚ) + 16 * (a (n - 4) : ℚ) by exact_mod_cast hq
  by_cases small : n < 6
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 6 ∨ n = 2 * k + 7 := by
    exact ⟨(n - 6) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = (-1) + (-10) * (4 : ℚ) ^ (k + 2) + 32 * (16 : ℚ) ^ (k + 2) := by
      rw [show n = 2 * (k + 2) + 2 by omega]
      exact value0 (k + 2)
    have v1 : (a (n - 4) : ℚ) = (-1) + (-10) * (4 : ℚ) ^ k + 32 * (16 : ℚ) ^ k := by
      rw [show n - 4 = 2 * k + 2 by omega]
      exact value0 k
    have v2 : (a (n - 1) : ℚ) = (-1) + (-28) * (4 : ℚ) ^ (k + 1) + 128 * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 1 = 2 * (k + 1) + 3 by omega]
      exact value1 (k + 1)
    have v3 : (a (n - 3) : ℚ) = (-1) + (-28) * (4 : ℚ) ^ k + 128 * (16 : ℚ) ^ k := by
      rw [show n - 3 = 2 * k + 3 by omega]
      exact value1 k
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p4 : (4 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 2) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p4, p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1) + (-28) * (4 : ℚ) ^ (k + 2) + 128 * (16 : ℚ) ^ (k + 2) := by
      rw [show n = 2 * (k + 2) + 3 by omega]
      exact value1 (k + 2)
    have v1 : (a (n - 4) : ℚ) = (-1) + (-28) * (4 : ℚ) ^ k + 128 * (16 : ℚ) ^ k := by
      rw [show n - 4 = 2 * k + 3 by omega]
      exact value1 k
    have v2 : (a (n - 1) : ℚ) = (-1) + (-10) * (4 : ℚ) ^ (k + 2) + 32 * (16 : ℚ) ^ (k + 2) := by
      rw [show n - 1 = 2 * (k + 2) + 2 by omega]
      exact value0 (k + 2)
    have v3 : (a (n - 3) : ℚ) = (-1) + (-10) * (4 : ℚ) ^ (k + 1) + 32 * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 3 = 2 * (k + 1) + 2 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p4 : (4 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 2) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p4, p16]
      all_goals ring

lemma claim2Tail : ∀ n : ℕ, 4 < n → (a n : ℚ) = -(-16 * (a (n - 4) : ℚ) + 20 * (a (n - 3) : ℚ) + -5 * (a (n - 1) : ℚ)) := by
  intro n hn
  by_cases small : n < 6
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1, initial2, initial3, initial4, initial5] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 6 ∨ n = 2 * k + 7 := by
    exact ⟨(n - 6) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = (-1) + (-10) * (4 : ℚ) ^ (k + 2) + 32 * (16 : ℚ) ^ (k + 2) := by
      rw [show n = 2 * (k + 2) + 2 by omega]
      exact value0 (k + 2)
    have v1 : (a (n - 1) : ℚ) = (-1) + (-28) * (4 : ℚ) ^ (k + 1) + 128 * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 1 = 2 * (k + 1) + 3 by omega]
      exact value1 (k + 1)
    have v2 : (a (n - 4) : ℚ) = (-1) + (-10) * (4 : ℚ) ^ k + 32 * (16 : ℚ) ^ k := by
      rw [show n - 4 = 2 * k + 2 by omega]
      exact value0 k
    have v3 : (a (n - 3) : ℚ) = (-1) + (-28) * (4 : ℚ) ^ k + 128 * (16 : ℚ) ^ k := by
      rw [show n - 3 = 2 * k + 3 by omega]
      exact value1 k
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p4 : (4 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 2) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p4, p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1) + (-28) * (4 : ℚ) ^ (k + 2) + 128 * (16 : ℚ) ^ (k + 2) := by
      rw [show n = 2 * (k + 2) + 3 by omega]
      exact value1 (k + 2)
    have v1 : (a (n - 1) : ℚ) = (-1) + (-10) * (4 : ℚ) ^ (k + 2) + 32 * (16 : ℚ) ^ (k + 2) := by
      rw [show n - 1 = 2 * (k + 2) + 2 by omega]
      exact value0 (k + 2)
    have v2 : (a (n - 4) : ℚ) = (-1) + (-28) * (4 : ℚ) ^ k + 128 * (16 : ℚ) ^ k := by
      rw [show n - 4 = 2 * k + 3 by omega]
      exact value1 k
    have v3 : (a (n - 3) : ℚ) = (-1) + (-10) * (4 : ℚ) ^ (k + 1) + 32 * (16 : ℚ) ^ (k + 1) := by
      rw [show n - 3 = 2 * (k + 1) + 2 by omega]
      exact value0 (k + 1)
    simp only [v0, v1, v2, v3]
    try rw [hk]
    all_goals
      have p4 : (4 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 2) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p4, p16]
      all_goals ring

open PowerSeries in
lemma claim2 : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X)) = 1 - 5 * X + 21 * X ^ 2 + 14 * X ^ 3 - 40 * X ^ 4 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  have hd : s * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X)) = PowerSeries.C (1 : ℚ) * (s * X ^ 0) + PowerSeries.C (-5 : ℚ) * (s * X ^ 1) + PowerSeries.C (20 : ℚ) * (s * X ^ 3) + PowerSeries.C (-16 : ℚ) * (s * X ^ 4) := by norm_num [map_ofNat] <;> ring
  have hn : 1 - 5 * X + 21 * X ^ 2 + 14 * X ^ 3 - 40 * X ^ 4 = PowerSeries.C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ) + PowerSeries.C (-5 : ℚ) * (X ^ 1 : PowerSeries ℚ) + PowerSeries.C (21 : ℚ) * (X ^ 2 : PowerSeries ℚ) + PowerSeries.C (14 : ℚ) * (X ^ 3 : PowerSeries ℚ) + PowerSeries.C (-40 : ℚ) * (X ^ 4 : PowerSeries ℚ) := by norm_num [map_ofNat] <;> ring
  rw [hd, hn]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_X_pow, coeff_mul_X_pow', s, coeff_mk]
  by_cases h : n ≤ 4
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4]
  · have hr := claim2Tail n (by omega)
    simp only [if_pos (show 4 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 1 ≤ n by omega), if_pos (show 0 ≤ n by omega), if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), Nat.sub_zero]
    linarith

lemma claim3 : ∀ n : ℕ, (a n : ℚ) = 2 * 4 ^ n - (((n % 2 : ℕ) : ℚ) * 2 + (if 0 < n then (1 : ℚ) else 0) * 5) * (2 : ℚ) ^ ((n : ℤ) - 1) - 1 := by
  intro n
  by_cases small : n < 2
  · interval_cases n <;> norm_num [Nat.odd_iff, Nat.even_iff, Int.toNat, Complex.I_pow_four, Complex.I_pow_three, Complex.I_sq, initial0, initial1] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    exact ⟨(n - 2) / 2, by omega⟩
  rcases hk with hk | hk
  · have v0 : (a n : ℚ) = (-1) + (-10) * (4 : ℚ) ^ k + 32 * (16 : ℚ) ^ k := by
      rw [show n = 2 * k + 2 by omega]
      exact value0 k
    have power1 : (4 : ℚ) ^ n = (16 : ℚ) ^ k * (4 : ℚ) ^ 2 := by
      rw [show n = 2 * k + 2 by omega, pow_add, pow_mul]
      norm_num
    have residue0 : n % 2 = 0 := by omega
    have hpos : 0 < n := by omega
    have zexp : (2 : ℚ) ^ ((n : ℤ)-1) = (4 : ℚ)^k * 2^1 := by
      rw [show (n : ℤ)-1 = ((2*k+1 : ℕ) : ℤ) by omega, zpow_natCast, pow_add, pow_mul]
      norm_num
    simp only [v0, power1, residue0, if_pos hpos, zexp]
    try rw [hk]
    all_goals
      have p4 : (4 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 2) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p4, p16]
      all_goals ring
  · have v0 : (a n : ℚ) = (-1) + (-28) * (4 : ℚ) ^ k + 128 * (16 : ℚ) ^ k := by
      rw [show n = 2 * k + 3 by omega]
      exact value1 k
    have power1 : (4 : ℚ) ^ n = (16 : ℚ) ^ k * (4 : ℚ) ^ 3 := by
      rw [show n = 2 * k + 3 by omega, pow_add, pow_mul]
      norm_num
    have residue0 : n % 2 = 1 := by omega
    have hpos : 0 < n := by omega
    have zexp : (2 : ℚ) ^ ((n : ℤ)-1) = (4 : ℚ)^k * 2^2 := by
      rw [show (n : ℤ)-1 = ((2*k+2 : ℕ) : ℤ) by omega, zpow_natCast, pow_add, pow_mul]
      norm_num
    simp only [v0, power1, residue0, if_pos hpos, zexp]
    try rw [hk]
    all_goals
      have p4 : (4 : ℚ) ^ k = (2 ^ k : ℚ) ^ 2 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 2) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      have p16 : (16 : ℚ) ^ k = (2 ^ k : ℚ) ^ 4 * (5 ^ k : ℚ) ^ 0 := by
        calc _ = (((2 : ℚ) ^ 4) * (5 ^ 0)) ^ k := by norm_num
             _ = _ := by rw [mul_pow, pow_right_comm, pow_right_comm (5 : ℚ)]
      push_cast
      norm_num [pow_succ, pow_add, pow_mul]
      all_goals try simp only [p4, p16]
      all_goals ring

theorem OMA.solution : type_of% @OMA.S_oeis_a267681.main := by
  exact ⟨claim1, claim2, claim3⟩
