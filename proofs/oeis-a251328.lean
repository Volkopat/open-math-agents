import OMAStatements.S_oeis_a251328
import Mathlib

namespace OMA.S_oeis_a251328

def cl : ℕ → Row → ℕ
  | 0, _ => 1
  | k + 1, r => (rows.map fun s => if fits r s then cl k s else 0).sum

theorem strips_len : ∀ (k : ℕ) (r : Row), (strips k r).length = cl k r := by
  intro k
  induction k with
  | zero => intro r; simp [strips, cl]
  | succ k ih =>
    intro r
    simp only [strips, cl, List.length_flatMap]
    refine congrArg List.sum ?_
    apply List.map_congr_left
    intro s _
    split_ifs <;> simp [ih]

theorem a_eq (n : ℕ) : a n = (rows.map (cl n)).sum := by
  simp only [a, List.length_flatMap, strips_len]

theorem cl_rec : ∀ k : ℕ, ∀ r : Row,
    cl (k + 4) r + 13 * cl (k + 2) r + 12 * cl (k + 1) r = 8 * cl (k + 3) r := by
  intro k
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    intro r
    have h1 : cl (k + 1 + 4) r = (rows.map fun s => if fits r s then cl (k + 4) s else 0).sum := rfl
    have h2 : cl (k + 1 + 2) r = (rows.map fun s => if fits r s then cl (k + 2) s else 0).sum := rfl
    have h3 : cl (k + 1 + 1) r = (rows.map fun s => if fits r s then cl (k + 1) s else 0).sum := rfl
    have h4 : cl (k + 1 + 3) r = (rows.map fun s => if fits r s then cl (k + 3) s else 0).sum := rfl
    rw [h1, h2, h3, h4, ← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
      ← List.sum_map_add, ← List.sum_map_add]
    refine congrArg List.sum ?_
    apply List.map_congr_left
    intro s _
    split_ifs
    · simpa using ih s
    · simp

theorem a_rec (k : ℕ) : a (k + 4) + 13 * a (k + 2) + 12 * a (k + 1) = 8 * a (k + 3) := by
  simp only [a_eq]
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
      ← List.sum_map_add, ← List.sum_map_add]
  refine congrArg List.sum ?_
  apply List.map_congr_left
  intro s _
  exact cl_rec k s

theorem a_vals : a 1 = 39 ∧ a 2 = 171 ∧ a 3 = 753 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem part1 : ∀ n : Nat, linearDenominator (quadraticDenominator seriesCoeff) n = polynomialNumerator n := by
  obtain ⟨h1, h2, h3⟩ := a_vals
  intro n
  rcases n with _ | _ | _ | _ | j
  · simp [linearDenominator, quadraticDenominator, shift, seriesCoeff, polynomialNumerator, constantSeries]
  · simp [linearDenominator, quadraticDenominator, shift, seriesCoeff, polynomialNumerator, constantSeries, h1]
  · simp [linearDenominator, quadraticDenominator, shift, seriesCoeff, polynomialNumerator, constantSeries, h1, h2]
  · simp [linearDenominator, quadraticDenominator, shift, seriesCoeff, polynomialNumerator, constantSeries, h1, h2, h3]
  · have h := a_rec j
    zify at h
    simp [linearDenominator, quadraticDenominator, shift, seriesCoeff, polynomialNumerator, constantSeries]
    linarith

theorem cnum_rec (n : ℕ) :
    closedNumerator (n + 3) = (8 * (closedNumerator (n + 2)).1 - 13 * (closedNumerator (n + 1)).1 - 12 * (closedNumerator n).1,
      8 * (closedNumerator (n + 2)).2 - 13 * (closedNumerator (n + 1)).2 - 12 * (closedNumerator n).2) := by
  apply Prod.ext
  · simp only [closedNumerator, qAdd, qMul, qPow]
    push_cast
    ring_nf
  · simp only [closedNumerator, qAdd, qMul, qPow]
    push_cast
    ring_nf

theorem part2 : ∀ n : ℕ, 1 ≤ n → closedNumerator n = (14 * (a n : Int), 0) := by
  obtain ⟨h1, h2, h3⟩ := a_vals
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n ≤ 3
    · interval_cases n
      · rw [h1]; decide +kernel
      · rw [h2]; decide +kernel
      · rw [h3]; decide +kernel
    · obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega⟩
      have h : closedNumerator (i + 4) = (8 * (closedNumerator (i + 3)).1 - 13 * (closedNumerator (i + 2)).1
          - 12 * (closedNumerator (i + 1)).1, 8 * (closedNumerator (i + 3)).2
          - 13 * (closedNumerator (i + 2)).2 - 12 * (closedNumerator (i + 1)).2) := cnum_rec (i + 1)
      rw [h, ih (i + 3) (by omega) (by omega), ih (i + 2) (by omega) (by omega),
        ih (i + 1) (by omega) (by omega)]
      have ha := a_rec i
      zify at ha
      apply Prod.ext
      · simp only
        linarith
      · simp

theorem solution_aux : type_of% @OMA.S_oeis_a251328.main := ⟨part1, part2⟩

end OMA.S_oeis_a251328

theorem OMA.solution : type_of% @OMA.S_oeis_a251328.main := OMA.S_oeis_a251328.solution_aux
