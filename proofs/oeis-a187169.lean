import OMAStatements.S_oeis_a187169
import Mathlib

open OMA.S_oeis_a187169

namespace P187169

theorem term (w : Profile) (h : w.2.1 ≤ 7 ∧ w.2.2.1 ≤ 7 ∧ w.2.2.2 ≤ 7) (k : ℕ) :
    placed (k+11) w = 4*placed (k+10) w - 6*placed (k+9) w + 4*placed (k+8) w - placed (k+7) w := by
  obtain ⟨c, a, b, e⟩ := w
  obtain ⟨ha, hb, he⟩ := h
  simp only at ha hb he
  simp only [placed, Nat.cast_sub (show a ≤ k + 7 by omega), Nat.cast_sub (show a ≤ k + 8 by omega), Nat.cast_sub (show a ≤ k + 9 by omega), Nat.cast_sub (show a ≤ k + 10 by omega), Nat.cast_sub (show a ≤ k + 11 by omega), Nat.cast_sub (show b ≤ k + 7 by omega), Nat.cast_sub (show b ≤ k + 8 by omega), Nat.cast_sub (show b ≤ k + 9 by omega), Nat.cast_sub (show b ≤ k + 10 by omega), Nat.cast_sub (show b ≤ k + 11 by omega), Nat.cast_sub (show e ≤ k + 7 by omega), Nat.cast_sub (show e ≤ k + 8 by omega), Nat.cast_sub (show e ≤ k + 9 by omega), Nat.cast_sub (show e ≤ k + 10 by omega), Nat.cast_sub (show e ≤ k + 11 by omega)]
  push_cast
  ring

theorem lsum (L : List Profile) (hL : ∀ w ∈ L, w.2.1 ≤ 7 ∧ w.2.2.1 ≤ 7 ∧ w.2.2.2 ≤ 7) (k : ℕ) :
    (L.map (placed (k+11))).sum = 4*(L.map (placed (k+10))).sum - 6*(L.map (placed (k+9))).sum + 4*(L.map (placed (k+8))).sum - (L.map (placed (k+7))).sum := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [term w (hL w (by simp)) k, ih (fun x hx => hL x (by simp [hx]))]
    ring

set_option maxHeartbeats 400000000 in
theorem spans : ∀ w ∈ shapes, w.2.1 ≤ 7 ∧ w.2.2.1 ≤ 7 ∧ w.2.2.2 ≤ 7 := by
  have h : shapes.all (fun w => decide (w.2.1 ≤ 7 ∧ w.2.2.1 ≤ 7 ∧ w.2.2.2 ≤ 7)) = true := by decide +kernel
  intro w hw
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

theorem rec2 (k : ℕ) : sequence (k+11) = 4*sequence (k+10) - 6*sequence (k+9) + 4*sequence (k+8) - sequence (k+7) := lsum shapes spans k

end P187169

set_option maxHeartbeats 400000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a187169.main := by
  refine ⟨fun n => ?_, P187169.rec2⟩
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> decide +kernel
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    have hr := P187169.rec2 k
    have hz : numerator (k + 11) = 0 := by
      unfold numerator
      split_ifs <;> first | omega | rfl
    simp only [lag, show 0 ≤ k + 11 by omega, show 1 ≤ k + 11 by omega, show 2 ≤ k + 11 by omega, show 3 ≤ k + 11 by omega, show 4 ≤ k + 11 by omega, if_true, Nat.sub_zero, show k + 11 - 1 = k + 10 by omega, show k + 11 - 2 = k + 9 by omega, show k + 11 - 3 = k + 8 by omega, show k + 11 - 4 = k + 7 by omega]
    rw [hz]
    linarith
