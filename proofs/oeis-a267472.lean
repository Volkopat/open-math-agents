import OMAStatements.S_oeis_a267472
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! OEIS A267472: closed form and order-five recurrence.

For `b < q`, the sum over `c` is `q ^ 2 - q + b + 1` (every `c ≠ b` contributes `q`), and the sum
over `a` is `(b + 1) ^ 2 + (q - 1) (q ^ 2 - q + b + 1)`. Summing over `b` gives
`6 * words q = 6 q ^ 4 - 7 q ^ 3 + 9 q ^ 2 - 2 q`. A polynomial of degree four is killed by the
fifth difference, which is the recurrence; the generating-series identity follows from it for
`m ≥ 6` and from the values `words 2, ..., words 6 = 12, 62, 204, 515, 1096` for `m ≤ 5`. -/

namespace OpenMath.A267472

open Finset OMA.S_oeis_a267472

private theorem inner (q b : ℕ) (hb : b < q) :
    ∑ c ∈ range q, (if c = b then (b : ℤ) + 1 else (q : ℤ)) = (q : ℤ) ^ 2 - q + b + 1 := by
  have h : ∀ c ∈ range q, (if c = b then (b : ℤ) + 1 else (q : ℤ)) =
      (q : ℤ) + (if c = b then (b : ℤ) + 1 - q else 0) := by
    intro c _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hb), nsmul_eq_mul]
  ring

private theorem middle (q b : ℕ) (hb : b < q) :
    (∑ a ∈ range q, if a = b then ((b : ℤ) + 1) ^ 2
      else ∑ c ∈ range q, if c = b then (b : ℤ) + 1 else (q : ℤ)) =
      ((b : ℤ) + 1) ^ 2 + ((q : ℤ) - 1) * ((q : ℤ) ^ 2 - q + b + 1) := by
  rw [inner q b hb]
  have h : ∀ a ∈ range q, (if a = b then ((b : ℤ) + 1) ^ 2 else (q : ℤ) ^ 2 - q + b + 1) =
      ((q : ℤ) ^ 2 - q + b + 1) +
        (if a = b then ((b : ℤ) + 1) ^ 2 - ((q : ℤ) ^ 2 - q + b + 1) else 0) := by
    intro a _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hb), nsmul_eq_mul]
  ring

private theorem outer (q : ℕ) : ∀ n : ℕ,
    6 * ∑ b ∈ range n, (((b : ℤ) + 1) ^ 2 + ((q : ℤ) - 1) * ((q : ℤ) ^ 2 - q + b + 1)) =
      2 * (n : ℤ) ^ 3 + 3 * (n : ℤ) ^ 2 + n + 6 * n * ((q : ℤ) - 1) * ((q : ℤ) ^ 2 - q + 1) +
        3 * ((q : ℤ) - 1) * n * (n - 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, mul_add, outer q n]
    push_cast
    ring

private theorem words_eq (q : ℕ) :
    6 * words q = 6 * (q : ℤ) ^ 4 - 7 * (q : ℤ) ^ 3 + 9 * (q : ℤ) ^ 2 - 2 * q := by
  unfold words
  rw [Finset.sum_congr rfl fun b hb => middle q b (Finset.mem_range.1 hb), outer q q]
  ring

private theorem coeff_succ (n : ℕ) : coeff (n + 1) = words (n + 2) := rfl

/-- The fifth difference of `words` vanishes. -/
private theorem rec_words (q : ℕ) :
    words (q + 5) = 5 * words (q + 4) - 10 * words (q + 3) + 10 * words (q + 2)
      - 5 * words (q + 1) + words q := by
  have h5 := words_eq (q + 5)
  have h4 := words_eq (q + 4)
  have h3 := words_eq (q + 3)
  have h2 := words_eq (q + 2)
  have h1 := words_eq (q + 1)
  have h0 := words_eq q
  push_cast at h5 h4 h3 h2 h1
  have e : 6 * (words (q + 5) - (5 * words (q + 4) - 10 * words (q + 3) + 10 * words (q + 2)
      - 5 * words (q + 1) + words q)) = 0 := by
    linear_combination h5 - 5 * h4 + 10 * h3 - 10 * h2 + 5 * h1 - h0
  clear h5 h4 h3 h2 h1 h0
  omega

private theorem rec5 (t : ℕ) :
    coeff (t + 6) = 5 * coeff (t + 5) - 10 * coeff (t + 4) + 10 * coeff (t + 3)
      - 5 * coeff (t + 2) + coeff (t + 1) := by
  show coeff (t + 5 + 1) = 5 * coeff (t + 4 + 1) - 10 * coeff (t + 3 + 1)
    + 10 * coeff (t + 2 + 1) - 5 * coeff (t + 1 + 1) + coeff (t + 1)
  rw [coeff_succ (t + 5), coeff_succ (t + 4), coeff_succ (t + 3), coeff_succ (t + 2),
    coeff_succ (t + 1), coeff_succ t]
  exact rec_words (t + 2)

theorem main :
    (∀ m, coeff m - 5*shift coeff 1 m + 10*shift coeff 2 m
      - 10*shift coeff 3 m + 5*shift coeff 4 m - shift coeff 5 m = numerator m) ∧
    (∀ t, coeff (t+6) = 5*coeff (t+5) - 10*coeff (t+4) + 10*coeff (t+3)
      - 5*coeff (t+2) + coeff (t+1)) := by
  refine ⟨fun m => ?_, rec5⟩
  rcases Nat.lt_or_ge m 6 with hm | hm
  · have w2 := words_eq 2
    have w3 := words_eq 3
    have w4 := words_eq 4
    have w5 := words_eq 5
    have w6 := words_eq 6
    norm_num at w2 w3 w4 w5 w6
    interval_cases m <;> simp [shift, coeff, numerator] <;> omega
  · obtain ⟨t, rfl⟩ : ∃ t, m = t + 6 := ⟨m - 6, by omega⟩
    have s1 : shift coeff 1 (t + 6) = coeff (t + 5) := if_pos (by omega)
    have s2 : shift coeff 2 (t + 6) = coeff (t + 4) := if_pos (by omega)
    have s3 : shift coeff 3 (t + 6) = coeff (t + 3) := if_pos (by omega)
    have s4 : shift coeff 4 (t + 6) = coeff (t + 2) := if_pos (by omega)
    have s5 : shift coeff 5 (t + 6) = coeff (t + 1) := if_pos (by omega)
    have hn : numerator (t + 6) = 0 := rfl
    rw [s1, s2, s3, s4, s5, hn, rec5 t]
    ring

end OpenMath.A267472

theorem OMA.solution : type_of% @OMA.S_oeis_a267472.main := OpenMath.A267472.main
