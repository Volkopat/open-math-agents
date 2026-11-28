import OMAStatements.S_oeis_a266787

namespace Ours

def update (l c r : Bool) : Bool :=
  (61 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)
def sweep (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: tail => update l c r :: sweep c r tail
def row : ℕ → Bool × List Bool
  | 0 => (false, [true])
  | n + 1 =>
    let (b, w) := row n
    (update b b b, sweep b b (w ++ [b, b]))
def a (n : ℕ) : ℕ :=
  Nat.ofDigits 10 ((row n).2.map Bool.toNat).reverse



namespace RowProof

def advance (s : Bool × List Bool) : Bool × List Bool :=
  (update s.1 s.1 s.1, sweep s.1 s.1 (s.2 ++ [s.1, s.1]))

lemma row_next (n : ℕ) : row (n + 1) = advance (row n) := rfl

def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, t => t
  | k + 1, t => w ++ blocks w k t

lemma blocks_append (w : List Bool) (k : ℕ) (t s : List Bool) :
    blocks w k t ++ s = blocks w k (t ++ s) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

lemma sweep_blocks (u v : List Bool) (l c : Bool)
    (h : ∀ t, sweep l c (u ++ t) = v ++ sweep l c t) (k : ℕ) (t : List Bool) :
    sweep l c (blocks u k t) = blocks v k (sweep l c t) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, h, ih]

lemma blocks_rotate (b : Bool) (w : List Bool) (k : ℕ) (t : List Bool) :
    blocks (b :: w) k (b :: t) = b :: blocks (w ++ [b]) k t := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, ih, List.cons_append, List.append_assoc, List.nil_append]

lemma seed0 : row 0 = (false, [true]) := rfl

lemma seed1 : row 1 = (true, [false, true, true]) :=
  (row_next 0).trans (by rw [seed0]; rfl)

lemma seed2 : row 2 = (false, [false, true, true, false, false]) :=
  (row_next 1).trans (by rw [seed1]; rfl)

lemma seed3 : row 3 = (true, [true, false, true, false, true, true, true]) :=
  (row_next 2).trans (by rw [seed2]; rfl)

lemma seed4 : row 4 = (false, [false, false, true, true, true, true, false, false, false]) :=
  (row_next 3).trans (by rw [seed3]; rfl)

lemma seed5 : row 5 = (true, [true, true, false, true, false, false, false, true, true, true, true]) :=
  (row_next 4).trans (by rw [seed4]; rfl)

lemma seed6 : row 6 = (false, [false, false, false, true, true, true, true, false, true, false, false, false, false]) :=
  (row_next 5).trans (by rw [seed5]; rfl)

lemma seed7 : row 7 = (true, [true, true, true, false, true, false, false, false, true, true, true, true, true, true, true]) :=
  (row_next 6).trans (by rw [seed6]; rfl)

lemma seed8 : row 8 = (false, [false, false, false, false, true, true, true, true, false, true, false, false, false, false, false, false, false]) :=
  (row_next 7).trans (by rw [seed7]; rfl)

lemma seed9 : row 9 = (true, [true, true, true, true, false, true, false, false, false, true, true, true, true, true, true, true, true, true, true]) :=
  (row_next 8).trans (by rw [seed8]; rfl)

lemma seed10 : row 10 = (false, [false, false, false, false, false, true, true, true, true, false, true, false, false, false, false, false, false, false, false, false, false]) :=
  (row_next 9).trans (by rw [seed9]; rfl)

lemma sweepBlock0 (k : ℕ) (t : List Bool) :
    sweep false false (blocks [false] k t) =
      blocks [true] k (sweep false false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock1 (k : ℕ) (t : List Bool) :
    sweep false false (blocks [false, false, false] k t) =
      blocks [true, true, true] k (sweep false false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock2 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true] k t) =
      blocks [false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock3 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true, true, true] k t) =
      blocks [false, false, false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma rotateBlock0 (k : ℕ) (t : List Bool) :
    blocks [false] k (false :: t) =
      false :: blocks [false] k t :=
  blocks_rotate _ [] k t

lemma rotateBlock1 (k : ℕ) (t : List Bool) :
    blocks [false, false, false] k (false :: t) =
      false :: blocks [false, false, false] k t :=
  blocks_rotate _ [false, false] k t

lemma rotateBlock2 (k : ℕ) (t : List Bool) :
    blocks [true] k (true :: t) =
      true :: blocks [true] k t :=
  blocks_rotate _ [] k t

lemma rotateBlock3 (k : ℕ) (t : List Bool) :
    blocks [true, true, true] k (true :: t) =
      true :: blocks [true, true, true] k t :=
  blocks_rotate _ [true, true] k t

lemma update000 : update false false false = true := by decide
lemma update001 : update false false true = false := by decide
lemma update010 : update false true false = true := by decide
lemma update011 : update false true true = true := by decide
lemma update100 : update true false false = true := by decide
lemma update101 : update true false true = true := by decide
lemma update110 : update true true false = false := by decide
lemma update111 : update true true true = false := by decide

def phase0 (k : ℕ) : Bool × List Bool :=
  (true, true :: true :: (blocks [true] k (false :: true :: false :: false :: false :: true :: true :: true :: true :: (blocks [true, true, true] k ([])))))

def phase1 (k : ℕ) : Bool × List Bool :=
  (false, false :: false :: (blocks [false] k (false :: true :: true :: true :: true :: false :: true :: false :: false :: (blocks [false, false, false] k (false :: false :: [])))))

lemma advance0 (k : ℕ) : advance (phase0 k) = phase1 k := by
  simp only [advance, phase0, phase1, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3]

lemma advance1 (k : ℕ) : advance (phase1 k) = phase0 (k + 1) := by
  simp only [advance, phase1, phase0, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma row_phases (k : ℕ) :
    row (2 * k + 5) = phase0 k ∧
    row (2 * k + 6) = phase1 k := by
  induction k with
  | zero => exact ⟨seed5, seed6⟩
  | succ k ih =>
    obtain ⟨_, old⟩ := ih
    have step0 : row (2 * (k + 1) + 5) = phase0 (k + 1) := by
      rw [show (2 * (k + 1) + 5) = (2 * k + 6) + 1 by omega, row_next (2 * k + 6), old, advance1]
    have step1 : row (2 * (k + 1) + 6) = phase1 (k + 1) := by
      rw [show (2 * (k + 1) + 6) = (2 * (k + 1) + 5) + 1 by omega, row_next (2 * (k + 1) + 5), step0, advance0]
    exact ⟨step0, step1⟩

lemma initial0 : a 0 = 1 := by
  rw [a, seed0] <;> rfl

lemma initial1 : a 1 = 11 := by
  rw [a, seed1] <;> rfl

lemma initial2 : a 2 = 1100 := by
  rw [a, seed2] <;> rfl

lemma initial3 : a 3 = 1010111 := by
  rw [a, seed3] <;> rfl

lemma initial4 : a 4 = 1111000 := by
  rw [a, seed4] <;> rfl

lemma initial5 : a 5 = 11010001111 := by
  rw [a, seed5] <;> rfl

lemma initial6 : a 6 = 1111010000 := by
  rw [a, seed6] <;> rfl

lemma initial7 : a 7 = 111010001111111 := by
  rw [a, seed7] <;> rfl

lemma initial8 : a 8 = 1111010000000 := by
  rw [a, seed8] <;> rfl

lemma initial9 : a 9 = 1111010001111111111 := by
  rw [a, seed9] <;> rfl

lemma initial10 : a 10 = 1111010000000000 := by
  rw [a, seed10] <;> rfl

def readBits (acc : ℚ) (w : List Bool) : ℚ :=
  w.foldl (fun z d => 10 * z + d.toNat) acc

lemma readCons (acc : ℚ) (d : Bool) (t : List Bool) :
    readBits acc (d :: t) = readBits (10 * acc + d.toNat) t := rfl

lemma readNil (acc : ℚ) : readBits acc [] = acc := rfl

lemma readDigits (w : List Bool) :
    ((Nat.ofDigits 10 (w.map Bool.toNat).reverse : ℕ) : ℚ) = readBits 0 w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton s d ih =>
    simp only [List.map_append, List.map_singleton, List.reverse_append, List.reverse_singleton,
      List.singleton_append, Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ih]
    simp [readBits, List.foldl_append]
    <;> ring

lemma readBlock0 (acc : ℚ) (k : ℕ) (t : List Bool) :
    readBits acc (blocks [false] k t) =
      readBits (acc * ((10 : ℚ) ^ k) ^ 1 + 0 * (((10 : ℚ) ^ k) ^ 1 - 1)) t := by
  induction k generalizing acc with
  | zero => simp [blocks]
  | succ k ih =>
    simp only [blocks, List.cons_append, List.nil_append, readCons, ih, pow_succ]
    congr 1 <;> norm_num [Bool.toNat] <;> ring

lemma readBlock1 (acc : ℚ) (k : ℕ) (t : List Bool) :
    readBits acc (blocks [false, false, false] k t) =
      readBits (acc * ((10 : ℚ) ^ k) ^ 3 + 0 * (((10 : ℚ) ^ k) ^ 3 - 1)) t := by
  induction k generalizing acc with
  | zero => simp [blocks]
  | succ k ih =>
    simp only [blocks, List.cons_append, List.nil_append, readCons, ih, pow_succ]
    congr 1 <;> norm_num [Bool.toNat] <;> ring

lemma readBlock2 (acc : ℚ) (k : ℕ) (t : List Bool) :
    readBits acc (blocks [true] k t) =
      readBits (acc * ((10 : ℚ) ^ k) ^ 1 + (1 / 9 : ℚ) * (((10 : ℚ) ^ k) ^ 1 - 1)) t := by
  induction k generalizing acc with
  | zero => simp [blocks]
  | succ k ih =>
    simp only [blocks, List.cons_append, List.nil_append, readCons, ih, pow_succ]
    congr 1 <;> norm_num [Bool.toNat] <;> ring

lemma readBlock3 (acc : ℚ) (k : ℕ) (t : List Bool) :
    readBits acc (blocks [true, true, true] k t) =
      readBits (acc * ((10 : ℚ) ^ k) ^ 3 + (1 / 9 : ℚ) * (((10 : ℚ) ^ k) ^ 3 - 1)) t := by
  induction k generalizing acc with
  | zero => simp [blocks]
  | succ k ih =>
    simp only [blocks, List.cons_append, List.nil_append, readCons, ih, pow_succ]
    congr 1 <;> norm_num [Bool.toNat] <;> ring

lemma rowValue0 (k : ℕ) : (a (2 * k + 5) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ k) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
  rw [a, (row_phases k).1, readDigits]
  simp only [phase0, readBlock0, readBlock1, readBlock2, readBlock3, readCons, readNil]
  norm_num [Bool.toNat] <;> ring

lemma rowValue1 (k : ℕ) : (a (2 * k + 6) : ℚ) = 1111010000 * ((10 : ℚ) ^ k) ^ 3 := by
  rw [a, (row_phases k).2, readDigits]
  simp only [phase1, readBlock0, readBlock1, readBlock2, readBlock3, readCons, readNil]
  norm_num [Bool.toNat] <;> ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma claim0 : ∀ n : ℕ, 10 < n → (a n : ℚ) = 11001 * (a (n - 2) : ℚ) - 10011000 * (a (n - 4) : ℚ) + 10000000 * (a (n - 6) : ℚ) := by
  intro n hn
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 11 ∨ n = k * 2 + 12 := ⟨(n - 11) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 11) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ (k + 3)) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ (k + 3)) ^ 4 := by
      rw [show k * 2 + 11 = (2 * (k + 3) + 5) by omega]
      exact rowValue0 (k + 3)
    have val2 : (a (k * 2 + 11 - 2) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ (k + 2)) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ (k + 2)) ^ 4 := by
      rw [show k * 2 + 11 - 2 = (2 * (k + 2) + 5) by omega]
      exact rowValue0 (k + 2)
    have val4 : (a (k * 2 + 11 - 4) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ (k + 1)) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 11 - 4 = (2 * (k + 1) + 5) by omega]
      exact rowValue0 (k + 1)
    have val6 : (a (k * 2 + 11 - 6) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ k) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 11 - 6 = (2 * k + 5) by omega]
      exact rowValue0 k
    simp only [val0, val2, val4, val6]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 12) : ℚ) = 1111010000 * ((10 : ℚ) ^ (k + 3)) ^ 3 := by
      rw [show k * 2 + 12 = (2 * (k + 3) + 6) by omega]
      exact rowValue1 (k + 3)
    have val2 : (a (k * 2 + 12 - 2) : ℚ) = 1111010000 * ((10 : ℚ) ^ (k + 2)) ^ 3 := by
      rw [show k * 2 + 12 - 2 = (2 * (k + 2) + 6) by omega]
      exact rowValue1 (k + 2)
    have val4 : (a (k * 2 + 12 - 4) : ℚ) = 1111010000 * ((10 : ℚ) ^ (k + 1)) ^ 3 := by
      rw [show k * 2 + 12 - 4 = (2 * (k + 1) + 6) by omega]
      exact rowValue1 (k + 1)
    have val6 : (a (k * 2 + 12 - 6) : ℚ) = 1111010000 * ((10 : ℚ) ^ k) ^ 3 := by
      rw [show k * 2 + 12 - 6 = (2 * k + 6) by omega]
      exact rowValue1 k
    simp only [val0, val2, val4, val6]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma convolution : ∀ n : ℕ, (1) * (if 0 ≤ n then (a (n - 0) : ℚ) else 0) + (-11001) * (if 2 ≤ n then (a (n - 2) : ℚ) else 0) + (10011000) * (if 4 ≤ n then (a (n - 4) : ℚ) else 0) + (-10000000) * (if 6 ≤ n then (a (n - 6) : ℚ) else 0) =
      (1) * (if n = 0 then (1 : ℚ) else 0) + (11) * (if n = 1 then (1 : ℚ) else 0) + (-9901) * (if n = 2 then (1 : ℚ) else 0) + (889100) * (if n = 3 then (1 : ℚ) else 0) + (-979100) * (if n = 4 then (1 : ℚ) else 0) + (7891000) * (if n = 5 then (1 : ℚ) else 0) + (-109001000) * (if n = 6 then (1 : ℚ) else 0) + (1090110000) * (if n = 7 then (1 : ℚ) else 0) + (9990000) * (if n = 8 then (1 : ℚ) else 0) + (-1100000000) * (if n = 9 then (1 : ℚ) else 0) + (100000000) * (if n = 10 then (1 : ℚ) else 0) := by
  intro n
  by_cases small : n < 11
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 11 ∨ n = k * 2 + 12 := ⟨(n - 11) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 11) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ (k + 3)) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ (k + 3)) ^ 4 := by
      rw [show k * 2 + 11 = (2 * (k + 3) + 5) by omega]
      exact rowValue0 (k + 3)
    have val2 : (a (k * 2 + 11 - 2) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ (k + 2)) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ (k + 2)) ^ 4 := by
      rw [show k * 2 + 11 - 2 = (2 * (k + 2) + 5) by omega]
      exact rowValue0 (k + 2)
    have val4 : (a (k * 2 + 11 - 4) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ (k + 1)) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 11 - 4 = (2 * (k + 1) + 5) by omega]
      exact rowValue0 (k + 1)
    have val6 : (a (k * 2 + 11 - 6) : ℚ) = (-1 / 9 : ℚ) + (-101110000) * ((10 : ℚ) ^ k) ^ 3 + (100000000000 / 9 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 11 - 6 = (2 * k + 5) by omega]
      exact rowValue0 k
    simp only [val0, val2, val4, val6, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 12) : ℚ) = 1111010000 * ((10 : ℚ) ^ (k + 3)) ^ 3 := by
      rw [show k * 2 + 12 = (2 * (k + 3) + 6) by omega]
      exact rowValue1 (k + 3)
    have val2 : (a (k * 2 + 12 - 2) : ℚ) = 1111010000 * ((10 : ℚ) ^ (k + 2)) ^ 3 := by
      rw [show k * 2 + 12 - 2 = (2 * (k + 2) + 6) by omega]
      exact rowValue1 (k + 2)
    have val4 : (a (k * 2 + 12 - 4) : ℚ) = 1111010000 * ((10 : ℚ) ^ (k + 1)) ^ 3 := by
      rw [show k * 2 + 12 - 4 = (2 * (k + 1) + 6) by omega]
      exact rowValue1 (k + 1)
    have val6 : (a (k * 2 + 12 - 6) : ℚ) = 1111010000 * ((10 : ℚ) ^ k) ^ 3 := by
      rw [show k * 2 + 12 - 6 = (2 * k + 6) by omega]
      exact rowValue1 k
    simp only [val0, val2, val4, val6, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

open PowerSeries

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma generating_function : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) =
      1 + 11 * X - 9901 * X ^ 2 + 889100 * X ^ 3 - 979100 * X ^ 4 + 7891000 * X ^ 5 - 109001000 * X ^ 6 + 1090110000 * X ^ 7 + 9990000 * X ^ 8 - 1100000000 * X ^ 9 + 100000000 * X ^ 10 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  calc
    _ = C (1 : ℚ) * (s * X ^ 0) + C (-11001 : ℚ) * (s * X ^ 2) + C (10011000 : ℚ) * (s * X ^ 4) + C (-10000000 : ℚ) * (s * X ^ 6) := by simp only [map_neg, map_one, map_ofNat] <;> ring
    _ = C (1 : ℚ) * (X ^ 0) + C (11 : ℚ) * (X ^ 1) + C (-9901 : ℚ) * (X ^ 2) + C (889100 : ℚ) * (X ^ 3) + C (-979100 : ℚ) * (X ^ 4) + C (7891000 : ℚ) * (X ^ 5) + C (-109001000 : ℚ) * (X ^ 6) + C (1090110000 : ℚ) * (X ^ 7) + C (9990000 : ℚ) * (X ^ 8) + C (-1100000000 : ℚ) * (X ^ 9) + C (100000000 : ℚ) * (X ^ 10) := by
      apply PowerSeries.ext
      intro n
      simp only [map_add, coeff_C_mul]
      simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
      exact convolution n
    _ = _ := by simp only [map_neg, map_one, map_ofNat] <;> ring

end RowProof

open RowProof


end Ours

section Helpers

open PowerSeries

lemma ps_eq_mul_inv {F N D : PowerSeries ℚ} (h : F * D = N) (hc : constantCoeff D ≠ 0) :
    F = N * D⁻¹ := by
  rw [← h, mul_assoc, PowerSeries.mul_inv_cancel D hc, mul_one]

lemma ps_int_of_rat {L R : PowerSeries ℤ}
    (h : PowerSeries.map (Int.castRingHom ℚ) L = PowerSeries.map (Int.castRingHom ℚ) R) :
    L = R := by
  ext n
  apply Int.cast_injective (α := ℚ)
  have hn := congr_arg (PowerSeries.coeff n) h
  simpa only [PowerSeries.coeff_map, Int.coe_castRingHom] using hn

lemma nat_div_of_floor {a X Y : ℕ} (hY : 0 < Y)
    (h : (a : ℤ) = ⌊(X : ℚ) / (Y : ℚ)⌋) : a = X / Y := by
  have hYq : (0 : ℚ) < (Y : ℚ) := by exact_mod_cast hY
  have hf := Int.floor_eq_iff.mp h.symm
  have h1 : (a : ℚ) * (Y : ℚ) ≤ (X : ℚ) := (le_div_iff₀ hYq).mp hf.1
  have h2 : (X : ℚ) < ((a : ℚ) + 1) * (Y : ℚ) := (div_lt_iff₀ hYq).mp hf.2
  have h1n : a * Y ≤ X := by exact_mod_cast h1
  have h2n : X < (a + 1) * Y := by exact_mod_cast h2
  have hle : a ≤ X / Y := (Nat.le_div_iff_mul_le hY).mpr h1n
  have hlt : X / Y < a + 1 := (Nat.div_lt_iff_lt_mul hY).mpr h2n
  omega

def seg (a : ℤ) : ℕ → (ℤ → Bool) → List Bool
  | 0, _ => []
  | m + 1, g => g a :: seg (a + 1) m g

lemma seg_snoc (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    seg a (m + 1) g = seg a m g ++ [g (a + m)] := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg, ih (a + 1), seg, List.cons_append]
    congr 2
    push_cast
    ring

lemma seg_append_two (a : ℤ) (m : ℕ) (g : ℤ → Bool) (b : Bool)
    (h1 : g (a + m) = b) (h2 : g (a + m + 1) = b) :
    seg a m g ++ [b, b] = seg a (m + 2) g := by
  rw [seg_snoc a (m + 1) g, seg_snoc a m g, List.append_assoc]
  simp only [List.singleton_append, Nat.cast_add, Nat.cast_one, ← add_assoc, h1, h2]

lemma seg_getElem? (a : ℤ) (m : ℕ) (g : ℤ → Bool) (k : ℕ) (hk : k < m) :
    (seg a m g)[k]? = some (g (a + k)) := by
  induction m generalizing a k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => simp [seg]
    | succ k =>
      simp only [seg, List.getElem?_cons_succ]
      rw [ih (a + 1) k (by omega)]
      congr 1
      push_cast
      ring

lemma seg_count (c : Bool) (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    (seg a m g).count c = ∑ k ∈ Finset.range m, if g (a + k) = c then 1 else 0 := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg_snoc, List.count_append, ih a, Finset.sum_range_succ]
    simp [List.count_cons, beq_iff_eq]

lemma seg_count_icc (n : ℕ) (g : ℤ → Bool) :
    (seg (-(n : ℤ)) (2 * n + 1) g).count true =
      ((Finset.Icc (-(n : ℤ)) n).filter (fun i => g i)).card := by
  rw [seg_count, Finset.card_filter]
  refine Finset.sum_nbij (fun k : ℕ => (k : ℤ) - n) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k₁ _ k₂ _ h
    dsimp only at h
    omega
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    refine ⟨(i + n).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp only
    omega
  · intro k _
    have h1 : -(n : ℤ) + (k : ℤ) = (k : ℤ) - n := by ring
    rw [h1]

lemma seg_ofDigits (B : ℕ) (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    Nat.ofDigits B (((seg a m g).map Bool.toNat).reverse) =
      ∑ k ∈ Finset.range m, if g (a + k) then B ^ (m - 1 - k) else 0 := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg_snoc, List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      Nat.ofDigits_cons, ih a, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_sub_cancel]
    have hsum :
        (∑ x ∈ Finset.range m, B * (if g (a + x) then B ^ (m - 1 - x) else 0)) =
          ∑ x ∈ Finset.range m, if g (a + x) then B ^ (m - x) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' := Finset.mem_range.mp hx
      split_ifs
      · rw [show m - x = (m - 1 - x) + 1 by omega, pow_succ']
      · simp
    rw [hsum]
    cases g (a + m) <;> simp [Nat.add_comm]

lemma seg_ofDigits_rev (B : ℕ) (n : ℕ) (g : ℤ → Bool) :
    Nat.ofDigits B (((seg (-(n : ℤ)) (2 * n + 1) g).map Bool.toNat).reverse) =
      ∑ i ∈ Finset.range (2 * n + 1), (g ((n : ℤ) - i)).toNat * B ^ i := by
  rw [seg_ofDigits, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hidx : -(n : ℤ) + ((2 * n + 1 - 1 - i : ℕ) : ℤ) = (n : ℤ) - i := by omega
  have hexp : 2 * n + 1 - 1 - (2 * n + 1 - 1 - i) = i := by omega
  rw [hidx, hexp]
  cases g ((n : ℤ) - i) <;> simp

end Helpers


section Extras

lemma seg_getElem! (a : ℤ) (m : ℕ) (g : ℤ → Bool) (k : ℕ) (hk : k < m) :
    (seg a m g)[k]! = g (a + k) := by
  induction m generalizing a k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => simp [seg]
    | succ k =>
      simp only [seg, List.getElem!_cons_succ]
      rw [ih (a + 1) k (by omega)]
      congr 1
      push_cast
      ring

end Extras

namespace BridgeProof

lemma sweep_seg_ours (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    Ours.sweep (g (a - 2)) (g (a - 1)) (seg a m g) =
      seg (a - 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    simp only [seg, Ours.sweep]
    refine congrArg₂ List.cons ?_ ?_
    · congr 1 <;> ring
    · calc
        Ours.sweep (g (a - 1)) (g a) (seg (a + 1) m g)
          = Ours.sweep (g ((a + 1) - 2)) (g ((a + 1) - 1)) (seg (a + 1) m g) := by
              congr 1 <;> ring
        _ = seg ((a + 1) - 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := ih (a + 1)
        _ = seg ((a - 1) + 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := by
              congr 1; ring

lemma st_step (n : ℕ) (i : ℤ) :
    OMA.S_oeis_a266787.state (n + 1) i = Ours.update (OMA.S_oeis_a266787.state n (i - 1)) (OMA.S_oeis_a266787.state n i) (OMA.S_oeis_a266787.state n (i + 1)) := by
  simp only [OMA.S_oeis_a266787.state]; cases OMA.S_oeis_a266787.state n (i - 1) <;> cases OMA.S_oeis_a266787.state n i <;> cases OMA.S_oeis_a266787.state n (i + 1) <;> rfl

lemma st_outside (n : ℕ) (i : ℤ) (hi : i < -(n : ℤ) ∨ (n : ℤ) < i) :
    OMA.S_oeis_a266787.state n i = (Ours.row n).1 := by
  induction n generalizing i with
  | zero =>
    have hne : i ≠ 0 := by omega
    simp [OMA.S_oeis_a266787.state, Ours.row, hne]
  | succ n ih =>
    rw [st_step, Ours.RowProof.row_next, Ours.RowProof.advance]
    have h1 : OMA.S_oeis_a266787.state n (i - 1) = (Ours.row n).1 := ih (i - 1) (by omega)
    have h2 : OMA.S_oeis_a266787.state n i = (Ours.row n).1 := ih i (by omega)
    have h3 : OMA.S_oeis_a266787.state n (i + 1) = (Ours.row n).1 := ih (i + 1) (by omega)
    rw [h1, h2, h3]

lemma row_eq_seg (n : ℕ) :
    (Ours.row n).2 = seg (-(n : ℤ)) (2 * n + 1) (OMA.S_oeis_a266787.state n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Ours.RowProof.row_next, Ours.RowProof.advance, ih]
    dsimp only
    have hr1 : OMA.S_oeis_a266787.state n (-(n : ℤ) + (2 * n + 1 : ℕ)) = (Ours.row n).1 :=
      st_outside n _ (by omega)
    have hr2 : OMA.S_oeis_a266787.state n (-(n : ℤ) + (2 * n + 1 : ℕ) + 1) = (Ours.row n).1 :=
      st_outside n _ (by omega)
    rw [seg_append_two (-(n : ℤ)) (2 * n + 1) (OMA.S_oeis_a266787.state n) (Ours.row n).1 hr1 hr2]
    have hl1 : (Ours.row n).1 = OMA.S_oeis_a266787.state n (-(n : ℤ) - 2) :=
      (st_outside n _ (by omega)).symm
    have hl2 : (Ours.row n).1 = OMA.S_oeis_a266787.state n (-(n : ℤ) - 1) :=
      (st_outside n _ (by omega)).symm
    conv_lhs =>
      arg 1; rw [hl1]
    conv_lhs =>
      arg 2; rw [hl2]
    rw [sweep_seg_ours]
    have ha : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have hm : 2 * n + 1 + 2 = 2 * (n + 1) + 1 := by omega
    have hf : (fun i => Ours.update (OMA.S_oeis_a266787.state n (i - 1)) (OMA.S_oeis_a266787.state n i) (OMA.S_oeis_a266787.state n (i + 1))) =
        OMA.S_oeis_a266787.state (n + 1) := by
      funext i
      exact (st_step n i).symm
    rw [ha, hm, hf]


lemma a_eq (n : ℕ) : OMA.S_oeis_a266787.a n = Ours.a n := by
  rw [Ours.a, row_eq_seg, seg_ofDigits, OMA.S_oeis_a266787.a]
  apply Finset.sum_congr rfl
  intro k _
  have hidx : -(n : ℤ) + (k : ℤ) = (k : ℤ) - n := by ring
  have hexp : 2 * n + 1 - 1 - k = 2 * n - k := by omega
  rw [hidx, hexp]

lemma main_proof : type_of% @OMA.S_oeis_a266787.main := by
  have ha : OMA.S_oeis_a266787.a = Ours.a := funext a_eq
  rw [ha]
  refine ⟨?_, ps_eq_mul_inv Ours.RowProof.generating_function (by simp)⟩
  intro n hn
  apply Int.cast_injective (α := ℚ)
  push_cast
  exact Ours.RowProof.claim0 n hn

end BridgeProof

theorem OMA.solution : type_of% @OMA.S_oeis_a266787.main := BridgeProof.main_proof
