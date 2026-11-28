import OMAStatements.S_oeis_a267257

open OMA.S_oeis_a267257

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
      blocks [true, true] k (sweep false false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock1 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true, true] k t) =
      blocks [false, false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma rotateBlock0 (k : ℕ) (t : List Bool) :
    blocks [false, false] k (false :: t) =
      false :: blocks [false, false] k t :=
  blocks_rotate _ [false] k t

lemma rotateBlock1 (k : ℕ) (t : List Bool) :
    blocks [true, true] k (true :: t) =
      true :: blocks [true, true] k t :=
  blocks_rotate _ [true] k t

lemma update000 : update false false false = true := by decide
lemma update001 : update false false true = true := by decide
lemma update010 : update false true false = true := by decide
lemma update011 : update false true true = true := by decide
lemma update100 : update true false false = false := by decide
lemma update101 : update true false true = true := by decide
lemma update110 : update true true false = true := by decide
lemma update111 : update true true true = false := by decide

def phase0 (k : ℕ) : Bool × List Bool :=
  (true, true :: true :: true :: true :: true :: true :: true :: (blocks [true, true] k (true :: true :: true :: (blocks [true, true] k (false :: false :: false :: true :: false :: [])))))

def phase1 (k : ℕ) : Bool × List Bool :=
  (false, false :: false :: false :: false :: false :: false :: false :: (blocks [false, false] k (false :: false :: false :: (blocks [false, false] k (true :: false :: true :: true :: true :: true :: true :: [])))))

lemma advance0 (k : ℕ) : advance (phase0 k) = phase1 k := by
  simp only [advance, phase0, phase1, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1]

lemma advance1 (k : ℕ) : advance (phase1 k) = phase0 (k + 1) := by
  simp only [advance, phase1, phase0, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1]

lemma row_phases (k : ℕ) :
    row (2 * k + 7) = phase0 k ∧
    row (2 * k + 8) = phase1 k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨_, old⟩ := ih
    have step0 : row (2 * (k + 1) + 7) = phase0 (k + 1) := by
      rw [show (2 * (k + 1) + 7) = (2 * k + 8) + 1 by omega, row_next (2 * k + 8), old, advance1]
    have step1 : row (2 * (k + 1) + 8) = phase1 (k + 1) := by
      rw [show (2 * (k + 1) + 8) = (2 * (k + 1) + 7) + 1 by omega, row_next (2 * (k + 1) + 7), step0, advance0]
    exact ⟨step0, step1⟩

lemma blocks_length (w : List Bool) (k : ℕ) (s : List Bool) :
    (blocks w k s).length = k * w.length + s.length := by
  induction k with
  | zero => simp [blocks]
  | succ k ih => simp [blocks, ih, Nat.succ_mul]; omega

lemma pick_append (u v : List Bool) (i : ℕ) :
    (u ++ v)[u.length + i]! = v[i]! := by
  induction u with
  | nil => simp
  | cons b u ih => simpa only [List.cons_append, List.length_cons, Nat.succ_add,
      List.getElem!_cons_succ] using ih

lemma rowValue0 (k : ℕ) : (centre (2 * k + 7) : ℚ) = 1 := by
  let pre : List Bool := true :: true :: true :: true :: true :: true :: true :: (blocks [true, true] k ([]))
  have splitRow : (phase0 k).2 = pre ++ (true :: true :: true :: (blocks [true, true] k (false :: false :: false :: true :: false :: []))) := by
    simp only [pre, phase0, List.cons_append, blocks_append, List.nil_append]
  have middle : 2 * k + 7 = pre.length + 0 := by
    simp [pre, blocks_length] <;> omega
  rw [centre, (row_phases k).1, splitRow, middle, pick_append, List.getElem!_cons_zero]
  rfl

lemma rowValue1 (k : ℕ) : (centre (2 * k + 8) : ℚ) = 0 := by
  let pre : List Bool := false :: false :: false :: false :: false :: false :: false :: (blocks [false, false] k (false :: []))
  have splitRow : (phase1 k).2 = pre ++ (false :: false :: (blocks [false, false] k (true :: false :: true :: true :: true :: true :: true :: []))) := by
    simp only [pre, phase1, List.cons_append, blocks_append, List.nil_append]
  have middle : 2 * k + 8 = pre.length + 0 := by
    simp [pre, blocks_length] <;> omega
  rw [centre, (row_phases k).2, splitRow, middle, pick_append, List.getElem!_cons_zero]
  rfl

lemma total_phases (k : ℕ) :
    (a (2 * k + 7) : ℚ) = (-1 / 99 : ℚ) + (1099999990 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 ∧
    (a (2 * k + 8) : ℚ) = (-10 / 99 : ℚ) + (10999999900 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 := by
  induction k with
  | zero =>
    norm_num [show a 7 = 11111111 by rfl, show a 8 = 111111110 by rfl]
  | succ k ih =>
    obtain ⟨_, old⟩ := ih
    have step0 : (a (2 * (k + 1) + 7) : ℚ) = (-1 / 99 : ℚ) + (1099999990 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 := by
      have addRow : a (2 * (k + 1) + 7) = 10 * a (2 * k + 8) + centre (2 * (k + 1) + 7) := by
        rw [show (2 * (k + 1) + 7) = (2 * k + 8) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, old, rowValue0]
      push_cast
      try simp only [pow_succ]
      ring
    have step1 : (a (2 * (k + 1) + 8) : ℚ) = (-10 / 99 : ℚ) + (10999999900 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 := by
      have addRow : a (2 * (k + 1) + 8) = 10 * a (2 * (k + 1) + 7) + centre (2 * (k + 1) + 8) := by
        rw [show (2 * (k + 1) + 8) = (2 * (k + 1) + 7) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, step0, rowValue1]
      push_cast
      try simp only [pow_succ]
      ring
    exact ⟨step0, step1⟩

lemma claim0 : ∀ n : ℕ, 5 < n → (a n : ℚ) = (-9 * (-1 : ℚ) ^ n + 109999999 * (2 : ℚ) ^ (n - 5) * (5 : ℚ) ^ (n - 6) - 11) / 198 := by
  intro n hn
  by_cases small : n < 7
  · interval_cases n <;> norm_num [show a 0 = 1 by rfl, show a 1 = 11 by rfl, show a 2 = 111 by rfl, show a 3 = 1111 by rfl, show a 4 = 11111 by rfl, show a 5 = 111111 by rfl, show a 6 = 1111111 by rfl] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 7 ∨ n = k * 2 + 8 := ⟨(n - 7) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 7) : ℚ) = (-1 / 99 : ℚ) + (1099999990 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 7 = (2 * k + 7) by omega]
      exact (total_phases k).1
    have powers0 (j : ℕ) : (-1 : ℚ) ^ (j * 2 + 7) = (-1) := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 7 = (j * 2 + 7) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp0 : (-1 : ℚ) ^ ((k * 2 + 7) : ℕ) = (-1) := by
      rw [show ((k * 2 + 7) : ℕ) = (k * 2 + 7) by omega]
      exact powers0 k
    have powers1 (j : ℕ) : (5 : ℚ) ^ (j * 2 + 1) = 5 * ((5 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 1 = (j * 2 + 1) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp1 : (5 : ℚ) ^ (((k * 2 + 7) : ℕ) - 6) = 5 * ((5 : ℚ) ^ k) ^ 2 := by
      rw [show (((k * 2 + 7) : ℕ) - 6) = (k * 2 + 1) by omega]
      exact powers1 k
    have powers2 (j : ℕ) : (2 : ℚ) ^ (j * 2 + 2) = 4 * ((2 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 2 = (j * 2 + 2) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp2 : (2 : ℚ) ^ (((k * 2 + 7) : ℕ) - 5) = 4 * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show (((k * 2 + 7) : ℕ) - 5) = (k * 2 + 2) by omega]
      exact powers2 k
    simp only [val0, exp0, exp1, exp2]
    <;> push_cast
    <;> norm_num [pow_add, show (10 : ℚ) ^ k = (2 : ℚ) ^ k * (5 : ℚ) ^ k by rw [← mul_pow]; norm_num, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 8) : ℚ) = (-10 / 99 : ℚ) + (10999999900 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 8 = (2 * k + 8) by omega]
      exact (total_phases k).2
    have powers0 (j : ℕ) : (-1 : ℚ) ^ (j * 2 + 8) = 1 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 8 = (j * 2 + 8) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp0 : (-1 : ℚ) ^ ((k * 2 + 8) : ℕ) = 1 := by
      rw [show ((k * 2 + 8) : ℕ) = (k * 2 + 8) by omega]
      exact powers0 k
    have powers1 (j : ℕ) : (5 : ℚ) ^ (j * 2 + 2) = 25 * ((5 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 2 = (j * 2 + 2) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp1 : (5 : ℚ) ^ (((k * 2 + 8) : ℕ) - 6) = 25 * ((5 : ℚ) ^ k) ^ 2 := by
      rw [show (((k * 2 + 8) : ℕ) - 6) = (k * 2 + 2) by omega]
      exact powers1 k
    have powers2 (j : ℕ) : (2 : ℚ) ^ (j * 2 + 3) = 8 * ((2 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 3 = (j * 2 + 3) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp2 : (2 : ℚ) ^ (((k * 2 + 8) : ℕ) - 5) = 8 * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show (((k * 2 + 8) : ℕ) - 5) = (k * 2 + 3) by omega]
      exact powers2 k
    simp only [val0, exp0, exp1, exp2]
    <;> push_cast
    <;> norm_num [pow_add, show (10 : ℚ) ^ k = (2 : ℚ) ^ k * (5 : ℚ) ^ k by rw [← mul_pow]; norm_num, pow_mul] <;> ring

lemma convolution : ∀ n : ℕ, (1) * (if 0 ≤ n then (a (n - 0) : ℚ) else 0) + (-10) * (if 1 ≤ n then (a (n - 1) : ℚ) else 0) + (-1) * (if 2 ≤ n then (a (n - 2) : ℚ) else 0) + (10) * (if 3 ≤ n then (a (n - 3) : ℚ) else 0) =
      (1) * (if n = 0 then (1 : ℚ) else 0) + (1) * (if n = 1 then (1 : ℚ) else 0) + (-1) * (if n = 8 then (1 : ℚ) else 0) := by
  intro n
  by_cases small : n < 10
  · interval_cases n <;> norm_num [show a 0 = 1 by rfl, show a 1 = 11 by rfl, show a 2 = 111 by rfl, show a 3 = 1111 by rfl, show a 4 = 11111 by rfl, show a 5 = 111111 by rfl, show a 6 = 1111111 by rfl, show a 7 = 11111111 by rfl, show a 8 = 111111110 by rfl, show a 9 = 1111111101 by rfl] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 10 ∨ n = k * 2 + 11 := ⟨(n - 10) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 10) : ℚ) = (-10 / 99 : ℚ) + (10999999900 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 := by
      rw [show k * 2 + 10 = (2 * (k + 1) + 8) by omega]
      exact (total_phases (k + 1)).2
    have val1 : (a (k * 2 + 10 - 1) : ℚ) = (-1 / 99 : ℚ) + (1099999990 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 := by
      rw [show k * 2 + 10 - 1 = (2 * (k + 1) + 7) by omega]
      exact (total_phases (k + 1)).1
    have val2 : (a (k * 2 + 10 - 2) : ℚ) = (-10 / 99 : ℚ) + (10999999900 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 10 - 2 = (2 * k + 8) by omega]
      exact (total_phases k).2
    have val3 : (a (k * 2 + 10 - 3) : ℚ) = (-1 / 99 : ℚ) + (1099999990 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 10 - 3 = (2 * k + 7) by omega]
      exact (total_phases k).1
    simp only [val0, val1, val2, val3, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 11) : ℚ) = (-1 / 99 : ℚ) + (1099999990 / 99 : ℚ) * ((10 : ℚ) ^ (k + 2)) ^ 2 := by
      rw [show k * 2 + 11 = (2 * (k + 2) + 7) by omega]
      exact (total_phases (k + 2)).1
    have val1 : (a (k * 2 + 11 - 1) : ℚ) = (-10 / 99 : ℚ) + (10999999900 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 := by
      rw [show k * 2 + 11 - 1 = (2 * (k + 1) + 8) by omega]
      exact (total_phases (k + 1)).2
    have val2 : (a (k * 2 + 11 - 2) : ℚ) = (-1 / 99 : ℚ) + (1099999990 / 99 : ℚ) * ((10 : ℚ) ^ (k + 1)) ^ 2 := by
      rw [show k * 2 + 11 - 2 = (2 * (k + 1) + 7) by omega]
      exact (total_phases (k + 1)).1
    have val3 : (a (k * 2 + 11 - 3) : ℚ) = (-10 / 99 : ℚ) + (10999999900 / 99 : ℚ) * ((10 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 11 - 3 = (2 * k + 8) by omega]
      exact (total_phases k).2
    simp only [val0, val1, val2, val3, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

open PowerSeries

lemma generating_function : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      1 + X - X ^ 8 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  calc
    _ = C (1 : ℚ) * (s * X ^ 0) + C (-10 : ℚ) * (s * X ^ 1) + C (-1 : ℚ) * (s * X ^ 2) + C (10 : ℚ) * (s * X ^ 3) := by simp only [map_neg, map_one, map_ofNat] <;> ring
    _ = C (1 : ℚ) * (X ^ 0) + C (1 : ℚ) * (X ^ 1) + C (-1 : ℚ) * (X ^ 8) := by
      apply PowerSeries.ext
      intro n
      simp only [map_add, coeff_C_mul]
      simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
      exact convolution n
    _ = _ := by simp only [map_neg, map_one, map_ofNat] <;> ring

end RowProof

open RowProof

theorem OMA.solution : type_of% @OMA.S_oeis_a267257.main :=
  ⟨claim0, generating_function⟩
