import OMAStatements.S_oeis_a294139
import Mathlib

/-!
# A294139: Barker's closed forms and recurrence

The summand is 3i² − 3ni + 2n², so the sum up to m is 3·m(m+1)(2m+1)/6 − 3n·m(m+1)/2 + 2n²m
(induction on m). Taking m = floor((n−1)/2) (= t − 1 for n = 2t, t for n = 2t + 1) gives both
closed forms (Sela Fried notes in the entry that they are true). Both are cubics with leading
coefficient 3/4, so their third differences with step 2 are the same constant; the recurrence is
the difference of these at n and n − 1, checked by substituting the closed forms.
-/

namespace PA294139

theorem partialSum (n m : ℕ) (hm : m ≤ n) :
    ((∑ i ∈ Finset.Icc 1 m, (2 * i ^ 2 + 2 * (n - i) ^ 2 + i * (n - i)) : ℕ) : ℚ) =
      3 * ((m : ℚ) * (m + 1) * (2 * m + 1) / 6) - 3 * (n : ℚ) * ((m : ℚ) * (m + 1) / 2) +
        2 * (n : ℚ) ^ 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega)]
    push_cast [Nat.cast_sub (show m + 1 ≤ n by omega)]
    ring

theorem closed (x : ℕ) :
    (OMA.S_oeis_a294139.a x : ℚ) =
      if x % 2 = 0 then (x : ℚ) * (6 * x - 1) * (x - 2) / 8 else (x : ℚ) * (3 * x - 1) * (x - 1) / 4 := by
  unfold OMA.S_oeis_a294139.a
  rw [partialSum x _ (by omega)]
  rcases Nat.even_or_odd' x with ⟨t, rfl | rfl⟩
  · rw [if_pos (by omega)]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · rw [show (2 * t - 1) / 2 = t - 1 by omega]
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [show s + 1 - 1 = s by omega]
      push_cast
      ring
  · rw [if_neg (by omega), show (2 * t + 1 - 1) / 2 = t by omega]
    push_cast
    ring

end PA294139

open OMA.S_oeis_a294139 in
theorem OMA.solution : type_of% @OMA.S_oeis_a294139.main := by
  refine ⟨fun n _ hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · rw [PA294139.closed, if_pos (Nat.even_iff.mp hn)]
  · rw [PA294139.closed, if_neg (by have := Nat.odd_iff.mp hn; omega)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
      show m + 7 - 7 = m by omega]
    have key : ((a (m + 7) : ℤ) : ℚ) =
        (((a (m + 6) : ℤ) + 3 * a (m + 5) -
          3 * a (m + 4) - 3 * a (m + 3) +
          3 * a (m + 2) + a (m + 1) -
          a m : ℤ) : ℚ) := by
      push_cast
      rw [PA294139.closed, PA294139.closed, PA294139.closed, PA294139.closed, PA294139.closed,
        PA294139.closed, PA294139.closed, PA294139.closed]
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · rw [if_neg (show ¬ (m + 7) % 2 = 0 by omega), if_pos (show (m + 6) % 2 = 0 by omega),
          if_neg (show ¬ (m + 5) % 2 = 0 by omega), if_pos (show (m + 4) % 2 = 0 by omega),
          if_neg (show ¬ (m + 3) % 2 = 0 by omega), if_pos (show (m + 2) % 2 = 0 by omega),
          if_neg (show ¬ (m + 1) % 2 = 0 by omega), if_pos h]
        push_cast
        ring
      · rw [if_pos (show (m + 7) % 2 = 0 by omega), if_neg (show ¬ (m + 6) % 2 = 0 by omega),
          if_pos (show (m + 5) % 2 = 0 by omega), if_neg (show ¬ (m + 4) % 2 = 0 by omega),
          if_pos (show (m + 3) % 2 = 0 by omega), if_neg (show ¬ (m + 2) % 2 = 0 by omega),
          if_pos (show (m + 1) % 2 = 0 by omega), if_neg (show ¬ m % 2 = 0 by omega)]
        push_cast
        ring
    exact_mod_cast key
