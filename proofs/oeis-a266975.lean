import OMAStatements.S_oeis_a266975

open OMA.S_oeis_a266975

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

lemma sweepBlock0 (k : ℕ) (t : List Bool) :
    sweep false false (blocks [false, false] k t) =
      blocks [false, false] k (sweep false false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock1 (k : ℕ) (t : List Bool) :
    sweep false true (blocks [false, true] k t) =
      blocks [true, false] k (sweep false true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock2 (k : ℕ) (t : List Bool) :
    sweep true false (blocks [true, false] k t) =
      blocks [false, true] k (sweep true false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma rotateBlock0 (k : ℕ) (t : List Bool) :
    blocks [false, false] k (false :: t) =
      false :: blocks [false, false] k t :=
  blocks_rotate _ [false] k t

lemma rotateBlock1 (k : ℕ) (t : List Bool) :
    blocks [false, true] k (false :: t) =
      false :: blocks [true, false] k t :=
  blocks_rotate _ [true] k t

lemma rotateBlock2 (k : ℕ) (t : List Bool) :
    blocks [true, false] k (true :: t) =
      true :: blocks [false, true] k t :=
  blocks_rotate _ [false] k t

lemma update000 : update false false false = false := by decide
lemma update001 : update false false true = true := by decide
lemma update010 : update false true false = true := by decide
lemma update011 : update false true true = true := by decide
lemma update100 : update true false false = false := by decide
lemma update101 : update true false true = false := by decide
lemma update110 : update true true false = true := by decide
lemma update111 : update true true true = false := by decide

def phase0 (k : ℕ) : Bool × List Bool :=
  (false, true :: true :: false :: true :: false :: (blocks [true, false] k (false :: false :: (blocks [false, false] k ([])))))

def phase1 (k : ℕ) : Bool × List Bool :=
  (false, true :: true :: true :: false :: true :: (blocks [false, true] k (false :: false :: (blocks [false, false] k (false :: false :: [])))))

lemma advance0 (k : ℕ) : advance (phase0 k) = phase1 k := by
  simp only [advance, phase0, phase1, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2]

lemma advance1 (k : ℕ) : advance (phase1 k) = phase0 (k + 1) := by
  simp only [advance, phase1, phase0, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2]

lemma row_phases (k : ℕ) :
    row (2 * k + 3) = phase0 k ∧
    row (2 * k + 4) = phase1 k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨_, old⟩ := ih
    have step0 : row (2 * (k + 1) + 3) = phase0 (k + 1) := by
      rw [show (2 * (k + 1) + 3) = (2 * k + 4) + 1 by omega, row_next (2 * k + 4), old, advance1]
    have step1 : row (2 * (k + 1) + 4) = phase1 (k + 1) := by
      rw [show (2 * (k + 1) + 4) = (2 * (k + 1) + 3) + 1 by omega, row_next (2 * (k + 1) + 3), step0, advance0]
    exact ⟨step0, step1⟩

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
    readBits acc (blocks [false, false] k t) =
      readBits (acc * ((10 : ℚ) ^ k) ^ 2 + 0 * (((10 : ℚ) ^ k) ^ 2 - 1)) t := by
  induction k generalizing acc with
  | zero => simp [blocks]
  | succ k ih =>
    simp only [blocks, List.cons_append, List.nil_append, readCons, ih, pow_succ]
    congr 1 <;> norm_num [Bool.toNat] <;> ring

lemma readBlock1 (acc : ℚ) (k : ℕ) (t : List Bool) :
    readBits acc (blocks [false, true] k t) =
      readBits (acc * ((10 : ℚ) ^ k) ^ 2 + (1 / 99 : ℚ) * (((10 : ℚ) ^ k) ^ 2 - 1)) t := by
  induction k generalizing acc with
  | zero => simp [blocks]
  | succ k ih =>
    simp only [blocks, List.cons_append, List.nil_append, readCons, ih, pow_succ]
    congr 1 <;> norm_num [Bool.toNat] <;> ring

lemma readBlock2 (acc : ℚ) (k : ℕ) (t : List Bool) :
    readBits acc (blocks [true, false] k t) =
      readBits (acc * ((10 : ℚ) ^ k) ^ 2 + (10 / 99 : ℚ) * (((10 : ℚ) ^ k) ^ 2 - 1)) t := by
  induction k generalizing acc with
  | zero => simp [blocks]
  | succ k ih =>
    simp only [blocks, List.cons_append, List.nil_append, readCons, ih, pow_succ]
    congr 1 <;> norm_num [Bool.toNat] <;> ring

lemma rowValue0 (k : ℕ) : (a (2 * k + 3) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
  rw [a, (row_phases k).1, readDigits]
  simp only [phase0, readBlock0, readBlock1, readBlock2, readCons, readNil]
  norm_num [Bool.toNat] <;> ring

lemma rowValue1 (k : ℕ) : (a (2 * k + 4) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
  rw [a, (row_phases k).2, readDigits]
  simp only [phase1, readBlock0, readBlock1, readBlock2, readCons, readNil]
  norm_num [Bool.toNat] <;> ring

lemma claim0 : ∀ n : ℕ, 0 < n → (a n : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 2) * (5 : ℚ) ^ (n - 1) * (9 * (-10 : ℚ) ^ n + 2189 * (10 : ℚ) ^ n - 20) / 99 := by
  intro n hn
  by_cases small : n < 3
  · interval_cases n <;> norm_num [show a 0 = 1 by rfl, show a 1 = 110 by rfl, show a 2 = 11100 by rfl] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 3 ∨ n = k * 2 + 4 := ⟨(n - 3) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 3) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 3 = (2 * k + 3) by omega]
      exact rowValue0 k
    have powers0 (j : ℕ) : (2 : ℚ) ^ (j * 2 + 1) = 2 * ((2 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 1 = (j * 2 + 1) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp0 : (2 : ℚ) ^ ((((k * 2 + 3) : ℕ) : ℤ) - 2) = 2 * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show ((((k * 2 + 3) : ℕ) : ℤ) - 2) = ((↑(k * 2 + 1) : ℤ)) by omega]
      exact powers0 k
    have powers1 (j : ℕ) : (5 : ℚ) ^ (j * 2 + 2) = 25 * ((5 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 2 = (j * 2 + 2) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp1 : (5 : ℚ) ^ (((k * 2 + 3) : ℕ) - 1) = 25 * ((5 : ℚ) ^ k) ^ 2 := by
      rw [show (((k * 2 + 3) : ℕ) - 1) = (k * 2 + 2) by omega]
      exact powers1 k
    have powers2 (j : ℕ) : (-10 : ℚ) ^ (j * 2 + 3) = (-1000) * ((2 : ℚ) ^ j) ^ 2 * ((5 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 3 = (j * 2 + 3) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp2 : (-10 : ℚ) ^ ((k * 2 + 3) : ℕ) = (-1000) * ((2 : ℚ) ^ k) ^ 2 * ((5 : ℚ) ^ k) ^ 2 := by
      rw [show ((k * 2 + 3) : ℕ) = (k * 2 + 3) by omega]
      exact powers2 k
    have powers3 (j : ℕ) : (10 : ℚ) ^ (j * 2 + 3) = 1000 * ((2 : ℚ) ^ j) ^ 2 * ((5 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 3 = (j * 2 + 3) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp3 : (10 : ℚ) ^ ((k * 2 + 3) : ℕ) = 1000 * ((2 : ℚ) ^ k) ^ 2 * ((5 : ℚ) ^ k) ^ 2 := by
      rw [show ((k * 2 + 3) : ℕ) = (k * 2 + 3) by omega]
      exact powers3 k
    simp only [val0, exp0, exp1, exp2, exp3]
    <;> push_cast
    <;> norm_num [pow_add, show (10 : ℚ) ^ k = (2 : ℚ) ^ k * (5 : ℚ) ^ k by rw [← mul_pow]; norm_num, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 4) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 4 = (2 * k + 4) by omega]
      exact rowValue1 k
    have powers0 (j : ℕ) : (2 : ℚ) ^ (j * 2 + 2) = 4 * ((2 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 2 = (j * 2 + 2) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp0 : (2 : ℚ) ^ ((((k * 2 + 4) : ℕ) : ℤ) - 2) = 4 * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show ((((k * 2 + 4) : ℕ) : ℤ) - 2) = ((↑(k * 2 + 2) : ℤ)) by omega]
      exact powers0 k
    have powers1 (j : ℕ) : (5 : ℚ) ^ (j * 2 + 3) = 125 * ((5 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 3 = (j * 2 + 3) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp1 : (5 : ℚ) ^ (((k * 2 + 4) : ℕ) - 1) = 125 * ((5 : ℚ) ^ k) ^ 2 := by
      rw [show (((k * 2 + 4) : ℕ) - 1) = (k * 2 + 3) by omega]
      exact powers1 k
    have powers2 (j : ℕ) : (-10 : ℚ) ^ (j * 2 + 4) = 10000 * ((2 : ℚ) ^ j) ^ 2 * ((5 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 4 = (j * 2 + 4) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp2 : (-10 : ℚ) ^ ((k * 2 + 4) : ℕ) = 10000 * ((2 : ℚ) ^ k) ^ 2 * ((5 : ℚ) ^ k) ^ 2 := by
      rw [show ((k * 2 + 4) : ℕ) = (k * 2 + 4) by omega]
      exact powers2 k
    have powers3 (j : ℕ) : (10 : ℚ) ^ (j * 2 + 4) = 10000 * ((2 : ℚ) ^ j) ^ 2 * ((5 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 4 = (j * 2 + 4) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp3 : (10 : ℚ) ^ ((k * 2 + 4) : ℕ) = 10000 * ((2 : ℚ) ^ k) ^ 2 * ((5 : ℚ) ^ k) ^ 2 := by
      rw [show ((k * 2 + 4) : ℕ) = (k * 2 + 4) by omega]
      exact powers3 k
    simp only [val0, exp0, exp1, exp2, exp3]
    <;> push_cast
    <;> norm_num [pow_add, show (10 : ℚ) ^ k = (2 : ℚ) ^ k * (5 : ℚ) ^ k by rw [← mul_pow]; norm_num, pow_mul] <;> ring

lemma claim1 : ∀ n : ℕ, 3 < n → (a n : ℚ) = 10 * (a (n - 1) : ℚ) + 10000 * (a (n - 2) : ℚ) - 100000 * (a (n - 3) : ℚ) := by
  intro n hn
  by_cases small : n < 6
  · interval_cases n <;> norm_num [show a 0 = 1 by rfl, show a 1 = 110 by rfl, show a 2 = 11100 by rfl, show a 3 = 1101000 by rfl, show a 4 = 111010000 by rfl, show a 5 = 11010100000 by rfl] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 6 ∨ n = k * 2 + 7 := ⟨(n - 6) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 6) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 6 = (2 * (k + 1) + 4) by omega]
      exact rowValue1 (k + 1)
    have val1 : (a (k * 2 + 6 - 1) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 6 - 1 = (2 * (k + 1) + 3) by omega]
      exact rowValue0 (k + 1)
    have val2 : (a (k * 2 + 6 - 2) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 6 - 2 = (2 * k + 4) by omega]
      exact rowValue1 k
    have val3 : (a (k * 2 + 6 - 3) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 6 - 3 = (2 * k + 3) by omega]
      exact rowValue0 k
    simp only [val0, val1, val2, val3]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 7) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 2)) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 2)) ^ 4 := by
      rw [show k * 2 + 7 = (2 * (k + 2) + 3) by omega]
      exact rowValue0 (k + 2)
    have val1 : (a (k * 2 + 7 - 1) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 7 - 1 = (2 * (k + 1) + 4) by omega]
      exact rowValue1 (k + 1)
    have val2 : (a (k * 2 + 7 - 2) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 7 - 2 = (2 * (k + 1) + 3) by omega]
      exact rowValue0 (k + 1)
    have val3 : (a (k * 2 + 7 - 3) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 7 - 3 = (2 * k + 4) by omega]
      exact rowValue1 k
    simp only [val0, val1, val2, val3]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

lemma convolution : ∀ n : ℕ, (1) * (if 0 ≤ n then (a (n - 0) : ℚ) else 0) + (-10) * (if 1 ≤ n then (a (n - 1) : ℚ) else 0) + (-10000) * (if 2 ≤ n then (a (n - 2) : ℚ) else 0) + (100000) * (if 3 ≤ n then (a (n - 3) : ℚ) else 0) =
      (1) * (if n = 0 then (1 : ℚ) else 0) + (100) * (if n = 1 then (1 : ℚ) else 0) + (-10000) * (if n = 3 then (1 : ℚ) else 0) := by
  intro n
  by_cases small : n < 6
  · interval_cases n <;> norm_num [show a 0 = 1 by rfl, show a 1 = 110 by rfl, show a 2 = 11100 by rfl, show a 3 = 1101000 by rfl, show a 4 = 111010000 by rfl, show a 5 = 11010100000 by rfl] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 6 ∨ n = k * 2 + 7 := ⟨(n - 6) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 6) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 6 = (2 * (k + 1) + 4) by omega]
      exact rowValue1 (k + 1)
    have val1 : (a (k * 2 + 6 - 1) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 6 - 1 = (2 * (k + 1) + 3) by omega]
      exact rowValue0 (k + 1)
    have val2 : (a (k * 2 + 6 - 2) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 6 - 2 = (2 * k + 4) by omega]
      exact rowValue1 k
    have val3 : (a (k * 2 + 6 - 3) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 6 - 3 = (2 * k + 3) by omega]
      exact rowValue0 k
    simp only [val0, val1, val2, val3, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 7) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 2)) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 2)) ^ 4 := by
      rw [show k * 2 + 7 = (2 * (k + 2) + 3) by omega]
      exact rowValue0 (k + 2)
    have val1 : (a (k * 2 + 7 - 1) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 7 - 1 = (2 * (k + 1) + 4) by omega]
      exact rowValue1 (k + 1)
    have val2 : (a (k * 2 + 7 - 2) : ℚ) = (-1000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 + (109000000 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 4 := by
      rw [show k * 2 + 7 - 2 = (2 * (k + 1) + 3) by omega]
      exact rowValue0 (k + 1)
    have val3 : (a (k * 2 + 7 - 3) : ℚ) = (-10000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 + (10990000000 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 4 := by
      rw [show k * 2 + 7 - 3 = (2 * k + 4) by omega]
      exact rowValue1 k
    simp only [val0, val1, val2, val3, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

open PowerSeries

lemma generating_function : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X)) =
      1 + 100 * X - 10000 * X ^ 3 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  calc
    _ = C (1 : ℚ) * (s * X ^ 0) + C (-10 : ℚ) * (s * X ^ 1) + C (-10000 : ℚ) * (s * X ^ 2) + C (100000 : ℚ) * (s * X ^ 3) := by simp only [map_neg, map_one, map_ofNat] <;> ring
    _ = C (1 : ℚ) * (X ^ 0) + C (100 : ℚ) * (X ^ 1) + C (-10000 : ℚ) * (X ^ 3) := by
      apply PowerSeries.ext
      intro n
      simp only [map_add, coeff_C_mul]
      simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
      exact convolution n
    _ = _ := by simp only [map_neg, map_one, map_ofNat] <;> ring

end RowProof

open RowProof

theorem OMA.solution : type_of% @OMA.S_oeis_a266975.main :=
  ⟨claim0, claim1, generating_function⟩
