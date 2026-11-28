import OMAStatements.S_mo_473119

namespace OMA.Mo473119
open Polynomial

noncomputable def rising (m : ℕ) : ℤ[X] := ascPochhammer ℤ m

noncomputable def rowA (P : ℤ[X]) : ℤ[X] := X * P

noncomputable def rowB (P : ℤ[X]) : ℤ[X] := X * (P.comp (X + 1) - P)

noncomputable def rowRun (f : ℕ) (P : ℤ[X]) : ℤ[X] := (rowB^[f]) (rowA P)

lemma rising_succ (m : ℕ) : rising (m + 1) = X * rising m + C (m : ℤ) * rising m := by
  simp only [rising, ascPochhammer_succ_right, C_eq_natCast]
  ring

lemma rising_coeff (m k : ℕ) : (rising m).coeff k = (Nat.stirlingFirst m k : ℤ) := by
  induction m generalizing k with
  | zero => cases k <;> simp [rising, coeff_one]
  | succ m ih =>
    rw [rising_succ, coeff_add, coeff_C_mul]
    cases k with
    | zero =>
      rw [coeff_X_mul_zero, ih]
      cases m <;> simp
    | succ k =>
      rw [coeff_X_mul, ih, ih, Nat.stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul]
      exact add_comm _ _

lemma rowA_rising (m : ℕ) : rowA (rising m) = rising (m + 1) - C (m : ℤ) * rising m := by
  rw [rowA, rising_succ, add_sub_cancel_right]

lemma rowB_rising (m : ℕ) : rowB (rising m) = C (m : ℤ) * rising m := by
  rw [rowB, mul_sub]
  change X * (ascPochhammer ℤ m).comp (X + 1) - X * rising m = _
  rw [← ascPochhammer_succ_left]
  change rising (m + 1) - X * rising m = _
  rw [rising_succ, add_sub_cancel_left]

lemma rowB_sub (P Q : ℤ[X]) : rowB (P - Q) = rowB P - rowB Q := by
  simp only [rowB, sub_comp]
  ring

lemma rowB_C_mul (c : ℤ) (P : ℤ[X]) : rowB (C c * P) = C c * rowB P := by
  simp only [rowB, mul_comp, C_comp]
  ring

lemma iterate_rowB_sub (f : ℕ) (P Q : ℤ[X]) :
    (rowB^[f]) (P - Q) = (rowB^[f]) P - (rowB^[f]) Q := by
  induction f with
  | zero => rfl
  | succ f ih => simp only [Function.iterate_succ_apply', ih, rowB_sub]

lemma iterate_rowB_C_mul (f : ℕ) (c : ℤ) (P : ℤ[X]) :
    (rowB^[f]) (C c * P) = C c * (rowB^[f]) P := by
  induction f with
  | zero => rfl
  | succ f ih => simp only [Function.iterate_succ_apply', ih, rowB_C_mul]

lemma iterate_rowB_rising (f m : ℕ) : (rowB^[f]) (rising m) = C ((m : ℤ)^f) * rising m := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Function.iterate_succ_apply', ih, rowB_C_mul, rowB_rising, pow_succ, map_mul, mul_assoc]

lemma rowRun_rising (f m : ℕ) :
    rowRun f (rising m) =
      C ((m + 1 : ℤ)^f) * rising (m + 1) - C ((m : ℤ)^(f + 1)) * rising m := by
  rw [rowRun, rowA_rising, iterate_rowB_sub, iterate_rowB_C_mul, iterate_rowB_rising, iterate_rowB_rising,
    Nat.cast_add, Nat.cast_one, pow_succ, map_mul]
  ring

end OMA.Mo473119

namespace OMA.Mo473119

open Polynomial OMA.S_mo_473119

noncomputable def applyRuns (runs : List ℕ) (P : ℤ[X]) : ℤ[X] :=
  runs.foldl (fun P f => rowRun f P) P

lemma rowRun_cmul (f : ℕ) (a : ℤ) (P : ℤ[X]) :
    rowRun f (C a * P) = C a * rowRun f P := by
  unfold rowRun rowA
  rw [mul_left_comm X, iterate_rowB_C_mul]

lemma rowRun_sub (f : ℕ) (P Q : ℤ[X]) :
    rowRun f (P - Q) = rowRun f P - rowRun f Q := by
  simp only [rowRun, rowA, mul_sub, iterate_rowB_sub]

lemma applyRuns_cmul (runs : List ℕ) (a : ℤ) (P : ℤ[X]) :
    applyRuns runs (C a * P) = C a * applyRuns runs P := by
  induction runs generalizing P with
  | nil => rfl
  | cons f runs ih =>
    change applyRuns runs (rowRun f (C a * P)) = C a * applyRuns runs (rowRun f P)
    rw [rowRun_cmul, ih]

lemma applyRuns_sub (runs : List ℕ) (P Q : ℤ[X]) :
    applyRuns runs (P - Q) = applyRuns runs P - applyRuns runs Q := by
  induction runs generalizing P Q with
  | nil => rfl
  | cons f runs ih =>
    change applyRuns runs (rowRun f (P - Q)) =
      applyRuns runs (rowRun f P) - applyRuns runs (rowRun f Q)
    rw [rowRun_sub, ih]

lemma reverseEntry_zero (runs : List ℕ) (m : ℕ) : reverseEntry runs m 0 = 0 := by
  cases runs <;> simp [reverseEntry]

lemma applyRuns_coeff (runs : List ℕ) (m i : ℕ) (hi : 0 < i) :
    (applyRuns runs (rising m)).coeff i = reverseEntry runs m (m + runs.length + 1 - i) := by
  induction runs generalizing m with
  | nil =>
    change (rising m).coeff i = reverseEntry [] m (m + 1 - i)
    rw [rising_coeff, reverseEntry]
    by_cases h : i ≤ m
    · have hindex : 0 < m + 1 - i ∧ m + 1 - i ≤ m := by omega
      have heq : m - (m + 1 - i) + 1 = i := by omega
      rw [if_pos hindex, heq]
    · have hindex : ¬(0 < m + 1 - i ∧ m + 1 - i ≤ m) := by omega
      rw [if_neg hindex, Nat.stirlingFirst_eq_zero_of_lt (by omega : m < i), Nat.cast_zero]
  | cons f runs ih =>
    change (applyRuns runs (rowRun f (rising m))).coeff i =
      reverseEntry (f :: runs) m (m + (runs.length + 1) + 1 - i)
    simp only [rowRun_rising, applyRuns_sub, applyRuns_cmul, coeff_sub, coeff_C_mul, ih]
    have hnext : m + 1 + runs.length + 1 - i = m + (runs.length + 1) + 1 - i := by omega
    have hprev : m + runs.length + 1 - i = (m + (runs.length + 1) + 1 - i) - 1 := by omega
    rw [hnext, hprev, reverseEntry]
    split
    · rename_i hzero
      simp [hzero, reverseEntry_zero]
    · rfl

end OMA.Mo473119

namespace OMA.Mo473119

open Polynomial OMA.S_mo_473119

lemma log2_bit_pos (b : Bool) (n : ℕ) (hn : n ≠ 0) :
    (Nat.bit b n).log2 = n.log2 + 1 := by
  have hs : Nat.bit b n >>> 1 ≠ 0 := by
    simpa only [Nat.bit_shiftRight_one] using hn
  simpa only [Nat.bit_shiftRight_one] using Nat.log2_eq_succ_log2_shiftRight hs

lemma remHigh_bit_pos (b : Bool) (n : ℕ) (hn : n ≠ 0) :
    remHigh (Nat.bit b n) = Nat.bit b (remHigh n) := by
  have hlo := (Nat.log2_eq_iff hn).mp rfl
  have hpow : 2 ^ n.log2 ≤ n := hlo.1
  simp only [remHigh, log2_bit_pos b n hn, pow_succ]
  cases b <;> simp only [Nat.bit_true_apply, Nat.bit_false_apply] <;> omega

lemma gap_bit_rem_pos (b : Bool) (n : ℕ) (hn : n ≠ 0)
    (hr : remHigh n ≠ 0) : gap (Nat.bit b n) = gap n := by
  rw [gap, gap, remHigh_bit_pos b n hn, if_neg (Nat.bit_ne_zero b hr), if_neg hr,
    log2_bit_pos b n hn, log2_bit_pos b (remHigh n) hr]
  omega

lemma runs_zero : runs 0 = [] := by
  rw [runs] <;> simp

lemma runs_pos (n : ℕ) (hn : n ≠ 0) :
    runs n = runs (remHigh n) ++ [gap n] := by
  conv_lhs => rw [runs]
  simp [hn]

lemma runs_ne_nil (n : ℕ) (hn : n ≠ 0) : runs n ≠ [] := by
  rw [runs_pos n hn]
  simp

lemma modify_head_append {xs ys : List ℕ} (h : xs ≠ []) :
    (xs ++ ys).modifyHead Nat.succ = xs.modifyHead Nat.succ ++ ys := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons a as => rfl

lemma runs_bit_pair (n : ℕ) :
    runs (Nat.bit true n) = 0 :: runs n ∧
      runs (Nat.bit false n) = (runs n).modifyHead Nat.succ := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn : n = 0
  · subst n
    have hn1 : remHigh 1 = 0 := by decide
    have hg1 : gap 1 = 0 := by decide
    simp only [Nat.bit_true_apply, Nat.bit_false_apply, Nat.mul_zero, Nat.zero_add,
      runs_zero, List.modifyHead_nil, and_true]
    rw [runs_pos 1 (by decide), hn1, hg1, runs_zero] <;> rfl
  · have hlt : remHigh n < n := by
      unfold remHigh
      exact Nat.sub_lt (Nat.pos_of_ne_zero hn) (by positivity)
    obtain ⟨it, iff⟩ := ih (remHigh n) hlt
    have hgt : gap (Nat.bit true n) = gap n := by
      by_cases hr : remHigh n = 0
      · simp only [gap, remHigh_bit_pos true n hn, log2_bit_pos true n hn, hr]
        norm_num [show Nat.log2 1 = 0 by decide] <;> omega
      · exact gap_bit_rem_pos true n hn hr
    constructor
    · rw [runs_pos _ (Nat.bit_ne_zero true hn), remHigh_bit_pos true n hn, hgt,
        it, runs_pos n hn] <;> rfl
    · rw [runs_pos _ (Nat.bit_ne_zero false hn), remHigh_bit_pos false n hn,
        runs_pos n hn]
      by_cases hr : remHigh n = 0
      · have hgf : gap (Nat.bit false n) = (gap n).succ := by
          rw [gap, gap, remHigh_bit_pos false n hn, log2_bit_pos false n hn, hr]
          simp
        rw [hgf, hr]
        simp [runs_zero]
      · rw [iff, gap_bit_rem_pos false n hn hr, modify_head_append (runs_ne_nil _ hr)]

lemma runs_length_bits (n : ℕ) : (runs n).length = n.bits.count true := by
  induction n using Nat.binaryRec' with
  | zero => simp [runs_zero]
  | bit b n h ih =>
    cases b
    · rw [(runs_bit_pair n).2, List.length_modifyHead, Nat.bits_append_bit n false h]
      simpa using ih
    · rw [(runs_bit_pair n).1, Nat.bits_append_bit n true h]
      simp [ih]

lemma row_bit {b : Bool} {n : ℕ} (h : n = 0 → b = true) :
    row (Nat.bit b n) = if b then rowA (row n) else rowB (row n) := by
  unfold row
  rw [Nat.binaryRec_eq b n (Or.inr h)] <;> cases b <;> rfl

lemma applyRuns_append (r s : List ℕ) (P : ℤ[X]) :
    applyRuns (r ++ s) P = applyRuns s (applyRuns r P) := by
  simp only [applyRuns, List.foldl_append]

lemma applyRuns_singleton (f : ℕ) (P : ℤ[X]) :
    applyRuns [f] P = rowRun f P := rfl

lemma row_eq_applyRuns (n : ℕ) : row n = applyRuns (runs n).reverse X := by
  induction n using Nat.binaryRec' with
  | zero => simp [row, runs_zero, applyRuns]
  | bit b n h ih =>
    rw [row_bit h]
    cases b
    · have hn : n ≠ 0 := fun hz => Bool.false_ne_true (h hz)
      rw [(runs_bit_pair n).2, if_neg Bool.false_ne_true, ih]
      cases hr : runs n with
      | nil => exact (runs_ne_nil n hn hr).elim
      | cons a as =>
        simp only [List.modifyHead_cons, List.reverse_cons, applyRuns_append,
          applyRuns_singleton, rowRun, Function.iterate_succ_apply']
    · rw [(runs_bit_pair n).1, if_pos rfl, ih, List.reverse_cons, applyRuns_append,
        applyRuns_singleton] <;> rfl

lemma rising_one : rising 1 = (X : ℤ[X]) := by
  simp [rising]

end OMA.Mo473119

open OMA.Mo473119 OMA.S_mo_473119 in
theorem OMA.solution : type_of% @OMA.S_mo_473119.main := by
  intro n k hk _
  rw [row_eq_applyRuns, ← rising_one, applyRuns_coeff _ 1 _ hk,
    List.length_reverse, runs_length_bits]
  unfold b
  have hidx : 1 + n.bits.count true + 1 - k = n.bits.count true + 2 - k := by omega
  rw [hidx]
