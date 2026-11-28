import OMAStatements.S_oeis_a266614

namespace Ours_oeis_a266614

def update (l c r : Bool) : Bool :=
  (41 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

def sweep (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: tail => update l c r :: sweep c r tail


def row : ℕ → Bool × List Bool
  | 0 => (false, [true])
  | n + 1 =>
    let (b, w) := row n
    (update b b b, sweep b b (w ++ [b, b]))

def a (n : ℕ) : ℕ := (row n).2.count true

end Ours_oeis_a266614

open Ours_oeis_a266614

namespace RowProof

def advance (s : Bool × List Bool) : Bool × List Bool :=
  (update s.1 s.1 s.1, sweep s.1 s.1 (s.2 ++ [s.1, s.1]))

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
    sweep false false (blocks [false, false, false, false, false, false, false, false] k t) =
      blocks [true, true, true, true, true, true, true, true] k (sweep false false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock1 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true, true, true, true, true, true, true, true] k t) =
      blocks [false, false, false, false, false, false, false, false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma rotateBlock0 (k : ℕ) (t : List Bool) :
    blocks [false, false, false, false, false, false, false, false] k (false :: t) =
      false :: blocks [false, false, false, false, false, false, false, false] k t :=
  blocks_rotate _ [false, false, false, false, false, false, false] k t

lemma rotateBlock1 (k : ℕ) (t : List Bool) :
    blocks [true, true, true, true, true, true, true, true] k (true :: t) =
      true :: blocks [true, true, true, true, true, true, true, true] k t :=
  blocks_rotate _ [true, true, true, true, true, true, true] k t

lemma update000 : update false false false = true := by decide
lemma update001 : update false false true = false := by decide
lemma update010 : update false true false = false := by decide
lemma update011 : update false true true = true := by decide
lemma update100 : update true false false = false := by decide
lemma update101 : update true false true = true := by decide
lemma update110 : update true true false = false := by decide
lemma update111 : update true true true = false := by decide

def phase0 (k : ℕ) : Bool × List Bool :=
  (false, (blocks [false, false, false, false, false, false, false, false] k (true :: [])))

def phase1 (k : ℕ) : Bool × List Bool :=
  (true, (blocks [true, true, true, true, true, true, true, true] k (false :: false :: false :: [])))

def phase2 (k : ℕ) : Bool × List Bool :=
  (false, (blocks [false, false, false, false, false, false, false, false] k (false :: false :: true :: false :: true :: [])))

def phase3 (k : ℕ) : Bool × List Bool :=
  (true, (blocks [true, true, true, true, true, true, true, true] k (true :: true :: false :: false :: true :: false :: false :: [])))

lemma advance0 (k : ℕ) : advance (phase0 k) = phase1 k := by
  simp only [advance, phase0, phase1, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1]

lemma advance1 (k : ℕ) : advance (phase1 k) = phase2 k := by
  simp only [advance, phase1, phase2, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1]

lemma advance2 (k : ℕ) : advance (phase2 k) = phase3 k := by
  simp only [advance, phase2, phase3, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1]

lemma advance3 (k : ℕ) : advance (phase3 k) = phase0 (k + 1) := by
  simp only [advance, phase3, phase0, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1]

lemma row_phases (k : ℕ) :
    row (4 * k + 0) = phase0 k ∧
    row (4 * k + 1) = phase1 k ∧
    row (4 * k + 2) = phase2 k ∧
    row (4 * k + 3) = phase3 k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨_, _, _, old⟩ := ih
    have step0 : row (4 * (k + 1) + 0) = phase0 (k + 1) := by
      rw [show (4 * (k + 1) + 0) = (4 * k + 3) + 1 by omega]
      change advance (row (4 * k + 3)) = _
      rw [old, advance3]
    have step1 : row (4 * (k + 1) + 1) = phase1 (k + 1) := by
      rw [show (4 * (k + 1) + 1) = (4 * (k + 1) + 0) + 1 by omega]
      change advance (row (4 * (k + 1) + 0)) = _
      rw [step0, advance0]
    have step2 : row (4 * (k + 1) + 2) = phase2 (k + 1) := by
      rw [show (4 * (k + 1) + 2) = (4 * (k + 1) + 1) + 1 by omega]
      change advance (row (4 * (k + 1) + 1)) = _
      rw [step1, advance1]
    have step3 : row (4 * (k + 1) + 3) = phase3 (k + 1) := by
      rw [show (4 * (k + 1) + 3) = (4 * (k + 1) + 2) + 1 by omega]
      change advance (row (4 * (k + 1) + 2)) = _
      rw [step2, advance2]
    exact ⟨step0, step1, step2, step3⟩

lemma count_blocks (w : List Bool) (k : ℕ) (s : List Bool) :
    (blocks w k s).count true = k * w.count true + s.count true := by
  induction k with
  | zero => simp [blocks]
  | succ k ih => simp [blocks, List.count_append, ih, Nat.succ_mul]; omega

lemma rowValue0 (k : ℕ) : (a (4 * k + 0) : ℚ) = 1 := by
  rw [a, (row_phases k).1]
  simp [phase0, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue1 (k : ℕ) : (a (4 * k + 1) : ℚ) = 8 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.1]
  simp [phase1, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue2 (k : ℕ) : (a (4 * k + 2) : ℚ) = 2 := by
  rw [a, (row_phases k).2.2.1]
  simp [phase2, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue3 (k : ℕ) : (a (4 * k + 3) : ℚ) = 3 + 8 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2]
  simp [phase3, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma claim0 : ∀ n : ℕ, 5 < n → (a n : ℚ) = (a (n - 2) : ℚ) + (a (n - 4) : ℚ) - (a (n - 6) : ℚ) := by
  intro n hn
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 4 + 6 ∨ n = k * 4 + 7 ∨ n = k * 4 + 8 ∨ n = k * 4 + 9 := ⟨(n - 6) / 4, by omega⟩
  rcases hk with rfl | rfl | rfl | rfl
  · have val0 : (a (k * 4 + 6) : ℚ) = 2 := by
      rw [show k * 4 + 6 = (4 * (k + 1) + 2) by omega]
      exact rowValue2 (k + 1)
    have val2 : (a (k * 4 + 6 - 2) : ℚ) = 1 := by
      rw [show k * 4 + 6 - 2 = (4 * (k + 1) + 0) by omega]
      exact rowValue0 (k + 1)
    have val4 : (a (k * 4 + 6 - 4) : ℚ) = 2 := by
      rw [show k * 4 + 6 - 4 = (4 * k + 2) by omega]
      exact rowValue2 k
    have val6 : (a (k * 4 + 6 - 6) : ℚ) = 1 := by
      rw [show k * 4 + 6 - 6 = (4 * k + 0) by omega]
      exact rowValue0 k
    simp only [val0, val2, val4, val6]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 4 + 7) : ℚ) = 3 + 8 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 4 + 7 = (4 * (k + 1) + 3) by omega]
      exact rowValue3 (k + 1)
    have val2 : (a (k * 4 + 7 - 2) : ℚ) = 8 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 4 + 7 - 2 = (4 * (k + 1) + 1) by omega]
      exact rowValue1 (k + 1)
    have val4 : (a (k * 4 + 7 - 4) : ℚ) = 3 + 8 * ((k : ℕ) : ℚ) := by
      rw [show k * 4 + 7 - 4 = (4 * k + 3) by omega]
      exact rowValue3 k
    have val6 : (a (k * 4 + 7 - 6) : ℚ) = 8 * ((k : ℕ) : ℚ) := by
      rw [show k * 4 + 7 - 6 = (4 * k + 1) by omega]
      exact rowValue1 k
    simp only [val0, val2, val4, val6]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 4 + 8) : ℚ) = 1 := by
      rw [show k * 4 + 8 = (4 * (k + 2) + 0) by omega]
      exact rowValue0 (k + 2)
    have val2 : (a (k * 4 + 8 - 2) : ℚ) = 2 := by
      rw [show k * 4 + 8 - 2 = (4 * (k + 1) + 2) by omega]
      exact rowValue2 (k + 1)
    have val4 : (a (k * 4 + 8 - 4) : ℚ) = 1 := by
      rw [show k * 4 + 8 - 4 = (4 * (k + 1) + 0) by omega]
      exact rowValue0 (k + 1)
    have val6 : (a (k * 4 + 8 - 6) : ℚ) = 2 := by
      rw [show k * 4 + 8 - 6 = (4 * k + 2) by omega]
      exact rowValue2 k
    simp only [val0, val2, val4, val6]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 4 + 9) : ℚ) = 8 * (((k + 2) : ℕ) : ℚ) := by
      rw [show k * 4 + 9 = (4 * (k + 2) + 1) by omega]
      exact rowValue1 (k + 2)
    have val2 : (a (k * 4 + 9 - 2) : ℚ) = 3 + 8 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 4 + 9 - 2 = (4 * (k + 1) + 3) by omega]
      exact rowValue3 (k + 1)
    have val4 : (a (k * 4 + 9 - 4) : ℚ) = 8 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 4 + 9 - 4 = (4 * (k + 1) + 1) by omega]
      exact rowValue1 (k + 1)
    have val6 : (a (k * 4 + 9 - 6) : ℚ) = 3 + 8 * ((k : ℕ) : ℚ) := by
      rw [show k * 4 + 9 - 6 = (4 * k + 3) by omega]
      exact rowValue3 k
    simp only [val0, val2, val4, val6]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

lemma convolution : ∀ n : ℕ, (1) * (if 0 ≤ n then (a (n - 0) : ℚ) else 0) + (-1) * (if 2 ≤ n then (a (n - 2) : ℚ) else 0) + (-1) * (if 4 ≤ n then (a (n - 4) : ℚ) else 0) + (1) * (if 6 ≤ n then (a (n - 6) : ℚ) else 0) =
      (1) * (if n = 0 then (1 : ℚ) else 0) + (1) * (if n = 2 then (1 : ℚ) else 0) + (3) * (if n = 3 then (1 : ℚ) else 0) + (-2) * (if n = 4 then (1 : ℚ) else 0) + (5) * (if n = 5 then (1 : ℚ) else 0) := by
  intro n
  by_cases small : n < 6
  · interval_cases n <;> norm_num [show a 0 = 1 by rfl, show a 1 = 0 by rfl, show a 2 = 2 by rfl, show a 3 = 3 by rfl, show a 4 = 1 by rfl, show a 5 = 8 by rfl] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 4 + 6 ∨ n = k * 4 + 7 ∨ n = k * 4 + 8 ∨ n = k * 4 + 9 := ⟨(n - 6) / 4, by omega⟩
  rcases hk with rfl | rfl | rfl | rfl
  · have val0 : (a (k * 4 + 6) : ℚ) = 2 := by
      rw [show k * 4 + 6 = (4 * (k + 1) + 2) by omega]
      exact rowValue2 (k + 1)
    have val2 : (a (k * 4 + 6 - 2) : ℚ) = 1 := by
      rw [show k * 4 + 6 - 2 = (4 * (k + 1) + 0) by omega]
      exact rowValue0 (k + 1)
    have val4 : (a (k * 4 + 6 - 4) : ℚ) = 2 := by
      rw [show k * 4 + 6 - 4 = (4 * k + 2) by omega]
      exact rowValue2 k
    have val6 : (a (k * 4 + 6 - 6) : ℚ) = 1 := by
      rw [show k * 4 + 6 - 6 = (4 * k + 0) by omega]
      exact rowValue0 k
    simp only [val0, val2, val4, val6, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 4 + 7) : ℚ) = 3 + 8 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 4 + 7 = (4 * (k + 1) + 3) by omega]
      exact rowValue3 (k + 1)
    have val2 : (a (k * 4 + 7 - 2) : ℚ) = 8 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 4 + 7 - 2 = (4 * (k + 1) + 1) by omega]
      exact rowValue1 (k + 1)
    have val4 : (a (k * 4 + 7 - 4) : ℚ) = 3 + 8 * ((k : ℕ) : ℚ) := by
      rw [show k * 4 + 7 - 4 = (4 * k + 3) by omega]
      exact rowValue3 k
    have val6 : (a (k * 4 + 7 - 6) : ℚ) = 8 * ((k : ℕ) : ℚ) := by
      rw [show k * 4 + 7 - 6 = (4 * k + 1) by omega]
      exact rowValue1 k
    simp only [val0, val2, val4, val6, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 4 + 8) : ℚ) = 1 := by
      rw [show k * 4 + 8 = (4 * (k + 2) + 0) by omega]
      exact rowValue0 (k + 2)
    have val2 : (a (k * 4 + 8 - 2) : ℚ) = 2 := by
      rw [show k * 4 + 8 - 2 = (4 * (k + 1) + 2) by omega]
      exact rowValue2 (k + 1)
    have val4 : (a (k * 4 + 8 - 4) : ℚ) = 1 := by
      rw [show k * 4 + 8 - 4 = (4 * (k + 1) + 0) by omega]
      exact rowValue0 (k + 1)
    have val6 : (a (k * 4 + 8 - 6) : ℚ) = 2 := by
      rw [show k * 4 + 8 - 6 = (4 * k + 2) by omega]
      exact rowValue2 k
    simp only [val0, val2, val4, val6, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 4 + 9) : ℚ) = 8 * (((k + 2) : ℕ) : ℚ) := by
      rw [show k * 4 + 9 = (4 * (k + 2) + 1) by omega]
      exact rowValue1 (k + 2)
    have val2 : (a (k * 4 + 9 - 2) : ℚ) = 3 + 8 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 4 + 9 - 2 = (4 * (k + 1) + 3) by omega]
      exact rowValue3 (k + 1)
    have val4 : (a (k * 4 + 9 - 4) : ℚ) = 8 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 4 + 9 - 4 = (4 * (k + 1) + 1) by omega]
      exact rowValue1 (k + 1)
    have val6 : (a (k * 4 + 9 - 6) : ℚ) = 3 + 8 * ((k : ℕ) : ℚ) := by
      rw [show k * 4 + 9 - 6 = (4 * k + 3) by omega]
      exact rowValue3 k
    simp only [val0, val2, val4, val6, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

open PowerSeries

lemma generating_function : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2)) =
      1 + X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4 + 5 * X ^ 5 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  calc
    _ = C (1 : ℚ) * (s * X ^ 0) + C (-1 : ℚ) * (s * X ^ 2) + C (-1 : ℚ) * (s * X ^ 4) + C (1 : ℚ) * (s * X ^ 6) := by simp only [map_neg, map_one, map_ofNat] <;> ring
    _ = C (1 : ℚ) * (X ^ 0) + C (1 : ℚ) * (X ^ 2) + C (3 : ℚ) * (X ^ 3) + C (-2 : ℚ) * (X ^ 4) + C (5 : ℚ) * (X ^ 5) := by
      apply PowerSeries.ext
      intro n
      simp only [map_add, coeff_C_mul]
      simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
      exact convolution n
    _ = _ := by simp only [map_neg, map_one, map_ofNat] <;> ring

end RowProof

open RowProof

open Ours_oeis_a266614
open PowerSeries in
lemma old_result :
    (∀ n : ℕ, 5 < n → (a n : ℚ) = (a (n - 2) : ℚ) + (a (n - 4) : ℚ) - (a (n - 6) : ℚ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2)) =
      1 + X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4 + 5 * X ^ 5) :=
  ⟨claim0, generating_function⟩

namespace Ours_oeis_a266614

def window (t : ℕ) (i : ℤ) : ℕ → List Bool
  | 0 => []
  | m + 1 => OMA.S_oeis_a266614.cell 41 t i :: window t (i + 1) m

lemma window_append (t : ℕ) (i : ℤ) (m k : ℕ) :
    window t i (m + k) = window t i m ++ window t (i + m) k := by
  induction m generalizing i with
  | zero => simp [window]
  | succ m ih =>
    rw [Nat.succ_add, window, window, List.cons_append, ih]
    congr 3 <;> push_cast <;> ring

lemma outside_window (t : ℕ) (i : ℤ) (hi : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    OMA.S_oeis_a266614.cell 41 t i = (row t).1 := by
  induction t generalizing i with
  | zero => simp [OMA.S_oeis_a266614.cell, row, show i ≠ 0 by omega]
  | succ t ih =>
    simp only [OMA.S_oeis_a266614.cell]
    rw [ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]
    rfl

lemma scan_window (t : ℕ) (i : ℤ) (m : ℕ) :
    sweep (OMA.S_oeis_a266614.cell 41 t (i - 2)) (OMA.S_oeis_a266614.cell 41 t (i - 1)) (window t i m) =
      window (t + 1) (i - 1) m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    simp only [window, sweep, List.cons.injEq]
    constructor
    · simp only [OMA.S_oeis_a266614.cell, show i - 1 - 1 = i - 2 by ring, show i - 1 + 1 = i by ring]
      rfl
    · simpa only [show i + 1 - 2 = i - 1 by ring, show i + 1 - 1 = i by ring,
        show i - 1 + 1 = i by ring] using ih (i + 1)

lemma row_window (t : ℕ) : (row t).2 = window t (-(t : ℤ)) (2 * t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change sweep ((row t).1) ((row t).1) ((row t).2 ++ [(row t).1, (row t).1]) = _
    let i := -(t : ℤ)
    have hr : window t (i + (2 * t + 1 : ℕ)) 2 = [(row t).1, (row t).1] := by
      simp only [window]
      rw [outside_window t (i + (2 * t + 1 : ℕ)) (by right; dsimp [i]; push_cast; omega),
          outside_window t (i + (2 * t + 1 : ℕ) + 1) (by right; dsimp [i]; push_cast; omega)]
    have hs := scan_window t i ((2 * t + 1) + 2)
    rw [outside_window t (i - 2) (by left; dsimp [i]; omega),
        outside_window t (i - 1) (by left; dsimp [i]; omega),
        window_append t i (2 * t + 1) 2, hr] at hs
    rw [ih]
    simpa only [i, Nat.cast_succ, show -(t : ℤ) - 1 = -((t : ℤ) + 1) by ring,
      show (2 * t + 1) + 2 = 2 * (t + 1) + 1 by omega] using hs

lemma window_count (t m : ℕ) (i : ℤ) :
    (window t i m).count true =
      ∑ j ∈ Finset.range m, if OMA.S_oeis_a266614.cell 41 t ((j : ℤ) + i) then 1 else 0 := by
  induction m generalizing i with
  | zero => simp [window]
  | succ m ih =>
    rw [window, List.count_cons, ih, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Int.zero_add, Nat.cast_zero,
      Int.add_right_comm _ 1 i, Int.add_assoc]
    cases OMA.S_oeis_a266614.cell 41 t i <;> simp

lemma row_on (t : ℕ) : ((row t).2).count true = OMA.S_oeis_a266614.onCount 41 t := by
  rw [row_window, window_count]
  simp only [OMA.S_oeis_a266614.onCount, sub_eq_add_neg]


lemma sequence_eq (n : ℕ) : OMA.S_oeis_a266614.a n = (a n : ℤ) := by
  exact congrArg (fun k : ℕ => (k : ℤ)) (row_on n).symm

end Ours_oeis_a266614

theorem OMA.solution : type_of% @OMA.S_oeis_a266614.main := by
  simp only [sequence_eq, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] 
  exact ⟨by
    intro n h
    first | exact old_result.1 n h | exact_mod_cast old_result.1 n h, old_result.2⟩
