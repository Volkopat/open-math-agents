import OMAStatements.S_oeis_a134449
import Mathlib

namespace A134449
open OMA.S_oeis_a134449 Finset

lemma even_sum (s n : ℕ) :
    2 * ∑ i ∈ range n, (-1 : ℤ) ^ (i * (2 * s)) * ((i * (2 * s) : ℕ) : ℤ) =
      2 * (s : ℤ) * ((n : ℤ) * ((n : ℤ) - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (-1 : ℤ) ^ (n * (2 * s)) = 1 := Even.neg_one_pow ⟨n * s, by ring⟩
    rw [sum_range_succ, mul_add, ih, he]
    push_cast
    ring

lemma row_even (s : ℕ) : row (2 * s) = 2 * (s : ℤ) ^ 2 * (2 * (s : ℤ) - 1) := by
  have h := even_sum s (2 * s)
  have e : (2 : ℤ) * (s : ℤ) * (((2 * s : ℕ) : ℤ) * (((2 * s : ℕ) : ℤ) - 1)) =
      2 * (2 * (s : ℤ) ^ 2 * (2 * (s : ℤ) - 1)) := by
    push_cast
    ring
  rw [e] at h
  unfold row
  linarith

lemma odd_sum (s t : ℕ) :
    ∑ i ∈ range (2 * t), (-1 : ℤ) ^ (i * (2 * s + 1)) * ((i * (2 * s + 1) : ℕ) : ℤ) =
      -((t : ℤ) * (2 * (s : ℤ) + 1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : 2 * (t + 1) = 2 * t + 1 + 1 := by ring
    have h1 : (-1 : ℤ) ^ (2 * t * (2 * s + 1)) = 1 :=
      Even.neg_one_pow ⟨t * (2 * s + 1), by ring⟩
    have h2 : (-1 : ℤ) ^ ((2 * t + 1) * (2 * s + 1)) = -1 :=
      Odd.neg_one_pow (Odd.mul ⟨t, rfl⟩ ⟨s, rfl⟩)
    rw [e, sum_range_succ, sum_range_succ, ih, h1, h2]
    push_cast
    ring

lemma row_odd (s : ℕ) : row (2 * s + 1) = (2 * (s : ℤ) + 1) * s := by
  unfold row
  have h1 : (-1 : ℤ) ^ (2 * s * (2 * s + 1)) = 1 :=
    Even.neg_one_pow ⟨s * (2 * s + 1), by ring⟩
  rw [sum_range_succ, odd_sum s s, h1]
  push_cast
  ring

lemma a_succ (n : ℕ) : a (n + 1) = a n + row (n + 1) := by
  unfold a
  rw [sum_range_succ]

lemma a_zero : a 0 = 0 := by
  simp [a, row]

lemma row_one : row 1 = 0 := by
  have r := row_odd 0
  simpa using r

lemma a_one : a 1 = 0 := by
  have h : a 1 = a 0 + row 1 := a_succ 0
  simp [h, a_zero, row_one]

lemma key (k : ℕ) :
    16 * a (2 * k) =
        (2 * (k : ℤ)) ^ 4 + 4 * (2 * (k : ℤ)) ^ 3 - 2 * (2 * (k : ℤ)) ^ 2 - 4 * (2 * (k : ℤ)) ∧
      16 * a (2 * k + 1) = (2 * (k : ℤ) + 1) ^ 4 - 1 := by
  induction k with
  | zero =>
    constructor
    · show 16 * a 0 = _
      rw [a_zero]
      norm_num
    · show 16 * a 1 = _
      rw [a_one]
      norm_num
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e1 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    have hA : a (2 * k + 1 + 1) = a (2 * k + 1) + row (2 * k + 1 + 1) := a_succ (2 * k + 1)
    rw [← e1] at hA
    have hB : a (2 * (k + 1) + 1) = a (2 * (k + 1)) + row (2 * (k + 1) + 1) :=
      a_succ (2 * (k + 1))
    have rE := row_even (k + 1)
    have rO := row_odd (k + 1)
    constructor
    · rw [hA, rE]
      push_cast
      linear_combination ih2
    · rw [hB, hA, rE, rO]
      push_cast
      linear_combination ih2

end A134449

theorem OMA.solution : type_of% @OMA.S_oeis_a134449.main := by
  intro n hn
  constructor
  · rintro ⟨k, rfl⟩
    have h := (A134449.key k).1
    rw [show k + k = 2 * k by ring]
    push_cast
    linear_combination h
  · rintro ⟨k, rfl⟩
    have h := (A134449.key k).2
    push_cast
    linear_combination h
