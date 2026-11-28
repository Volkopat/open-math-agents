import OMAStatements.S_oeis_a267294

namespace Ours_oeis_a267294

def ruleOut (left center right : Bool) : Bool :=
  (121 : ℕ).testBit (4 * left.toNat + 2 * center.toNat + right.toNat)


def cell : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => ruleOut (cell n (i - 1)) (cell n i) (cell n (i + 1))


def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

end Ours_oeis_a267294

namespace ProofA267294

open Ours_oeis_a267294
open PowerSeries

def live : ℕ → ℤ → Prop
  | 0, i => i = 0
  | 1, i => i ≠ -1 ∧ i ≠ 0
  | 2, i => i = -2 ∨ i = -1 ∨ i = 1
  | 3, i => i ≠ -3 ∧ i ≠ 1
  | 4, i => i = -4 ∨ i = -3 ∨ i = -2 ∨ i = 0 ∨ i = 1 ∨ i = 2
  | 5, i => i ≠ -5 ∧ i ≠ -3 ∧ i ≠ 1
  | 6, i => i = -6 ∨ i = -5 ∨ i = -3 ∨ i = -2 ∨ i = 0 ∨ i = 1 ∨ i = 2
  | m + 7, i =>
    let d := i + ((m + 7 : ℕ) : ℤ)
    if m % 4 = 0 then d ≠ 0 ∧ d ≠ 8
    else if m % 4 = 1 then d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 8 ∨ d = 9 ∨ d = 10
    else if m % 4 = 2 then d ≠ 0 ∧ d ≠ 2 ∧ d ≠ 8 ∧ d ≠ 10
    else d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 8 ∨ d = 9 ∨ d = 11 ∨ d = 12

def liveDec (n : ℕ) (i : ℤ) : Bool :=
  match n with
  | 0 => decide (i = 0)
  | 1 => decide (i ≠ -1 ∧ i ≠ 0)
  | 2 => decide (i = -2 ∨ i = -1 ∨ i = 1)
  | 3 => decide (i ≠ -3 ∧ i ≠ 1)
  | 4 => decide (i = -4 ∨ i = -3 ∨ i = -2 ∨ i = 0 ∨ i = 1 ∨ i = 2)
  | 5 => decide (i ≠ -5 ∧ i ≠ -3 ∧ i ≠ 1)
  | 6 => decide (i = -6 ∨ i = -5 ∨ i = -3 ∨ i = -2 ∨ i = 0 ∨ i = 1 ∨ i = 2)
  | m + 7 =>
    let d := i + ((m + 7 : ℕ) : ℤ)
    if m % 4 = 0 then decide (d ≠ 0 ∧ d ≠ 8)
    else if m % 4 = 1 then decide (d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 8 ∨ d = 9 ∨ d = 10)
    else if m % 4 = 2 then decide (d ≠ 0 ∧ d ≠ 2 ∧ d ≠ 8 ∧ d ≠ 10)
    else decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 8 ∨ d = 9 ∨ d = 11 ∨ d = 12)

lemma liveDec_iff (n : ℕ) (i : ℤ) : liveDec n i = true ↔ live n i := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => simp [liveDec, live]
  | m + 7 =>
    dsimp [liveDec, live]
    split_ifs <;> simp

lemma rule121_table (l c r : Bool) :
    ruleOut l c r = true ↔
      ((¬l = true) ∧ (c = true ↔ r = true)) ∨
      (l = true ∧ ¬(c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma live_step (n : ℕ) (i : ℤ) :
    (((¬live n (i - 1)) ∧ (live n i ↔ live n (i + 1))) ∨
      (live n (i - 1) ∧ ¬(live n i ∧ live n (i + 1)))) ↔ live (n + 1) i := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 =>
    dsimp [live]; omega
  | 6 =>
    change _ ↔ live (0 + 7) i
    dsimp [live]; omega
  | m + 7 =>
    change _ ↔ live ((m + 1) + 7) i
    dsimp [live]
    split_ifs <;> push_cast <;> omega

lemma cell_iff_live (n : ℕ) (i : ℤ) : cell n i = true ↔ live n i := by
  induction n generalizing i with
  | zero => simp [cell, live]
  | succ n ih =>
    rw [cell, rule121_table, ih, ih, ih]
    exact live_step n i

lemma cell_eq_liveDec (n : ℕ) (i : ℤ) : cell n i = liveDec n i :=
  Bool.eq_iff_iff.mpr ((cell_iff_live n i).trans (liveDec_iff n i).symm)

def fastA (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if liveDec n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

lemma a_eq_fastA (n : ℕ) : a n = fastA n := by
  unfold a fastA
  simp only [cell_eq_liveDec]

lemma liveDec_period (m j : ℕ) :
    liveDec (m + 11) ((j : ℤ) - ((m + 11 : ℕ) : ℤ)) =
      liveDec (m + 7) ((j : ℤ) - ((m + 7 : ℕ) : ℤ)) := by
  apply Bool.eq_iff_iff.mpr
  rw [liveDec_iff, liveDec_iff]
  change live ((m + 4) + 7) _ ↔ live (m + 7) _
  dsimp [live]
  split_ifs <;> push_cast <;> omega

lemma liveDec_tail (m j : ℕ) (hj : 13 ≤ j) :
    liveDec (m + 7) ((j : ℤ) - ((m + 7 : ℕ) : ℤ)) = decide (m % 2 = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [liveDec_iff, decide_eq_true_eq]
  dsimp [live]
  split_ifs <;> push_cast <;> omega

lemma step_four (m : ℕ) :
    fastA (m + 11) = 256 * fastA (m + 7) +
      ∑ k ∈ Finset.range 8, if decide (m % 2 = 0) then (2 : ℤ) ^ (7 - k) else 0 := by
  unfold fastA
  rw [show 2 * (m + 11) + 1 = (2 * (m + 7) + 1) + 8 by omega, Finset.sum_range_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [liveDec_period m j, show 2 * (m + 11) - j = (2 * (m + 7) - j) + 8 by omega, pow_add]
    split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have htail := liveDec_tail (m + 4) (2 * (m + 7) + 1 + k) (by omega)
    rw [show (m + 4) + 7 = m + 11 by omega, show (m + 4) % 2 = m % 2 by omega] at htail
    rw [htail, show 2 * (m + 11) - (2 * (m + 7) + 1 + k) = 7 - k by omega]

lemma recurrence (n : ℕ) (hn : 12 < n) :
    a n = a (n - 2) + 256 * a (n - 4) - 256 * a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
  simp only [show m + 13 - 2 = m + 11 by omega, show m + 13 - 4 = m + 9 by omega,
    show m + 13 - 6 = m + 7 by omega, a_eq_fastA]
  have h1 := step_four (m + 2)
  have h0 := step_four m
  rw [show m + 2 + 11 = m + 13 by omega, show m + 2 + 7 = m + 9 by omega,
      show (m + 2) % 2 = m % 2 by omega] at h1
  linarith

lemma initials :
    fastA 0 = 1 ∧ fastA 1 = 1 ∧ fastA 2 = 26 ∧ fastA 3 = 59 ∧
    fastA 4 = 476 ∧ fastA 5 = 751 ∧ fastA 6 = 7024 ∧
    fastA 7 = 16319 ∧ fastA 8 = 115136 ∧
    fastA 9 = 195327 ∧ fastA 10 = 1776384 ∧
    fastA 11 = 4177919 ∧ fastA 12 = 29474816 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma generating :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2)) =
      1 + X + 25 * X ^ 2 + 58 * X ^ 3 + 194 * X ^ 4 + 436 * X ^ 5 +
        148 * X ^ 6 + 720 * X ^ 7 - 7088 * X ^ 8 +
        1856 * X ^ 9 - 15040 * X ^ 10 - 2816 * X ^ 11 +
        21760 * X ^ 12 := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have hprod : F * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2)) =
      F - F * X ^ 2 - C 256 * (F * X ^ 4) + C 256 * (F * X ^ 6) := by
    simp only [map_ofNat]
    ring
  have hrhs : (1 + X + 25 * X ^ 2 + 58 * X ^ 3 + 194 * X ^ 4 + 436 * X ^ 5 +
        148 * X ^ 6 + 720 * X ^ 7 - 7088 * X ^ 8 +
        1856 * X ^ 9 - 15040 * X ^ 10 - 2816 * X ^ 11 +
        21760 * X ^ 12 : PowerSeries ℚ) =
      1 + X ^ 1 * C 1 + X ^ 2 * C 25 + X ^ 3 * C 58 + X ^ 4 * C 194 +
        X ^ 5 * C 436 + X ^ 6 * C 148 + X ^ 7 * C 720 -
        X ^ 8 * C 7088 + X ^ 9 * C 1856 - X ^ 10 * C 15040 -
        X ^ 11 * C 2816 + X ^ 12 * C 21760 := by
    simp only [map_ofNat, map_one]; ring
  rw [hprod, hrhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow_mul', coeff_one, F, coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := initials
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [coeff_C, a_eq_fastA, h0]
  · simp [coeff_C, a_eq_fastA, h1]
  · simp [coeff_C, a_eq_fastA, h0, h2]; norm_num
  · simp [coeff_C, a_eq_fastA, h1, h3]; norm_num
  · simp [coeff_C, a_eq_fastA, h0, h2, h4]; norm_num
  · simp [coeff_C, a_eq_fastA, h1, h3, h5]; norm_num
  · simp [coeff_C, a_eq_fastA, h0, h2, h4, h6]; norm_num
  · simp [coeff_C, a_eq_fastA, h1, h3, h5, h7]; norm_num
  · simp [coeff_C, a_eq_fastA, h2, h4, h6, h8]; norm_num
  · simp [coeff_C, a_eq_fastA, h3, h5, h7, h9]; norm_num
  · simp [coeff_C, a_eq_fastA, h4, h6, h8, h10]; norm_num
  · simp [coeff_C, a_eq_fastA, h5, h7, h9, h11]; norm_num
  · simp [coeff_C, a_eq_fastA, h6, h8, h10, h12]; norm_num
  · simp only [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 13 by ring]
    have hr : (a (m + 13) : ℚ) = (a (m + 11) : ℚ) + 256 * (a (m + 9) : ℚ) - 256 * (a (m + 7) : ℚ) := by
      simpa [show m + 13 - 2 = m + 11 by omega, show m + 13 - 4 = m + 9 by omega,
             show m + 13 - 6 = m + 7 by omega] using
        (show (a (m + 13) : ℚ) = (a (m + 13 - 2) : ℚ) + 256 * (a (m + 13 - 4) : ℚ) -
            256 * (a (m + 13 - 6) : ℚ) from by
          exact_mod_cast recurrence (m + 13) (by omega))
    simp [coeff_C]
    linarith

end ProofA267294

open Ours_oeis_a267294
open PowerSeries in
lemma old_result :
    (∀ n : ℕ, 12 < n → a n = a (n - 2) + 256 * a (n - 4) - 256 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2)) =
      1 + X + 25 * X ^ 2 + 58 * X ^ 3 + 194 * X ^ 4 + 436 * X ^ 5 +
        148 * X ^ 6 + 720 * X ^ 7 - 7088 * X ^ 8 +
        1856 * X ^ 9 - 15040 * X ^ 10 - 2816 * X ^ 11 +
        21760 * X ^ 12) :=
  ⟨ProofA267294.recurrence, ProofA267294.generating⟩

namespace Ours_oeis_a267294

lemma cell_eq (n : ℕ) (i : ℤ) : OMA.S_oeis_a267294.cell 121 n i = cell n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [OMA.S_oeis_a267294.cell, cell, ih] <;> rfl

lemma sequence_eq (n : ℕ) : OMA.S_oeis_a267294.a n = a n := by
  simp only [OMA.S_oeis_a267294.a, a, cell_eq]

end Ours_oeis_a267294

theorem OMA.solution : type_of% @OMA.S_oeis_a267294.main := by
  simp only [sequence_eq, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] 
  exact ⟨by
    intro n h
    first | exact old_result.1 n h | exact_mod_cast old_result.1 n h, old_result.2⟩
