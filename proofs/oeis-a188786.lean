import OMAStatements.S_oeis_a188786
import Mathlib

open OMA.S_oeis_a188786

namespace P188786

theorem term (w : Profile) (h : w.2.1 ≤ 2 ∧ w.2.2.1 ≤ 2 ∧ w.2.2.2.1 ≤ 2 ∧ w.2.2.2.2 ≤ 2) (k : ℕ) :
    placed (k+7) w = 5*placed (k+6) w - 10*placed (k+5) w + 10*placed (k+4) w - 5*placed (k+3) w + placed (k+2) w := by
  obtain ⟨c, a, b, e, f⟩ := w
  obtain ⟨ha, hb, he, hf⟩ := h
  simp only at ha hb he hf
  simp only [placed, Nat.cast_sub (show a ≤ k + 2 by omega), Nat.cast_sub (show a ≤ k + 3 by omega), Nat.cast_sub (show a ≤ k + 4 by omega), Nat.cast_sub (show a ≤ k + 5 by omega), Nat.cast_sub (show a ≤ k + 6 by omega), Nat.cast_sub (show a ≤ k + 7 by omega), Nat.cast_sub (show b ≤ k + 2 by omega), Nat.cast_sub (show b ≤ k + 3 by omega), Nat.cast_sub (show b ≤ k + 4 by omega), Nat.cast_sub (show b ≤ k + 5 by omega), Nat.cast_sub (show b ≤ k + 6 by omega), Nat.cast_sub (show b ≤ k + 7 by omega), Nat.cast_sub (show e ≤ k + 2 by omega), Nat.cast_sub (show e ≤ k + 3 by omega), Nat.cast_sub (show e ≤ k + 4 by omega), Nat.cast_sub (show e ≤ k + 5 by omega), Nat.cast_sub (show e ≤ k + 6 by omega), Nat.cast_sub (show e ≤ k + 7 by omega), Nat.cast_sub (show f ≤ k + 2 by omega), Nat.cast_sub (show f ≤ k + 3 by omega), Nat.cast_sub (show f ≤ k + 4 by omega), Nat.cast_sub (show f ≤ k + 5 by omega), Nat.cast_sub (show f ≤ k + 6 by omega), Nat.cast_sub (show f ≤ k + 7 by omega)]
  push_cast
  ring

theorem lsum (L : List Profile) (hL : ∀ w ∈ L, w.2.1 ≤ 2 ∧ w.2.2.1 ≤ 2 ∧ w.2.2.2.1 ≤ 2 ∧ w.2.2.2.2 ≤ 2) (k : ℕ) :
    (L.map (placed (k+7))).sum = 5*(L.map (placed (k+6))).sum - 10*(L.map (placed (k+5))).sum + 10*(L.map (placed (k+4))).sum - 5*(L.map (placed (k+3))).sum + (L.map (placed (k+2))).sum := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [term w (hL w (by simp)) k, ih (fun x hx => hL x (by simp [hx]))]
    ring

theorem spans : ∀ w ∈ shapes, w.2.1 ≤ 2 ∧ w.2.2.1 ≤ 2 ∧ w.2.2.2.1 ≤ 2 ∧ w.2.2.2.2 ≤ 2 := by
  have h : shapes.all (fun w => decide (w.2.1 ≤ 2 ∧ w.2.2.1 ≤ 2 ∧ w.2.2.2.1 ≤ 2 ∧ w.2.2.2.2 ≤ 2)) = true := by decide +kernel
  intro w hw
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

theorem rec2 (k : ℕ) : sequence (k+7) = 5*sequence (k+6) - 10*sequence (k+5) + 10*sequence (k+4) - 5*sequence (k+3) + sequence (k+2) := lsum shapes spans k

end P188786

theorem OMA.solution : type_of% @OMA.S_oeis_a188786.main := by
  refine ⟨fun n => ?_, P188786.rec2⟩
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> decide +kernel
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    have hr := P188786.rec2 k
    have hz : numerator (k + 7) = 0 := by
      unfold numerator
      split_ifs <;> first | omega | rfl
    simp only [lag, show 0 ≤ k + 7 by omega, show 1 ≤ k + 7 by omega, show 2 ≤ k + 7 by omega, show 3 ≤ k + 7 by omega, show 4 ≤ k + 7 by omega, show 5 ≤ k + 7 by omega, if_true, Nat.sub_zero, show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega]
    rw [hz]
    linarith
