import OMAStatements.S_oeis_a187168
import Mathlib

open OMA.S_oeis_a187168

namespace P187168

theorem term (w : Profile) (h : w.2.1 ≤ 6 ∧ w.2.2.1 ≤ 6 ∧ w.2.2.2 ≤ 6) (k : ℕ) :
    placed (k+10) w = 4*placed (k+9) w - 6*placed (k+8) w + 4*placed (k+7) w - placed (k+6) w := by
  obtain ⟨c, a, b, e⟩ := w
  obtain ⟨ha, hb, he⟩ := h
  simp only at ha hb he
  simp only [placed, Nat.cast_sub (show a ≤ k + 6 by omega), Nat.cast_sub (show a ≤ k + 7 by omega), Nat.cast_sub (show a ≤ k + 8 by omega), Nat.cast_sub (show a ≤ k + 9 by omega), Nat.cast_sub (show a ≤ k + 10 by omega), Nat.cast_sub (show b ≤ k + 6 by omega), Nat.cast_sub (show b ≤ k + 7 by omega), Nat.cast_sub (show b ≤ k + 8 by omega), Nat.cast_sub (show b ≤ k + 9 by omega), Nat.cast_sub (show b ≤ k + 10 by omega), Nat.cast_sub (show e ≤ k + 6 by omega), Nat.cast_sub (show e ≤ k + 7 by omega), Nat.cast_sub (show e ≤ k + 8 by omega), Nat.cast_sub (show e ≤ k + 9 by omega), Nat.cast_sub (show e ≤ k + 10 by omega)]
  push_cast
  ring

theorem lsum (L : List Profile) (hL : ∀ w ∈ L, w.2.1 ≤ 6 ∧ w.2.2.1 ≤ 6 ∧ w.2.2.2 ≤ 6) (k : ℕ) :
    (L.map (placed (k+10))).sum = 4*(L.map (placed (k+9))).sum - 6*(L.map (placed (k+8))).sum + 4*(L.map (placed (k+7))).sum - (L.map (placed (k+6))).sum := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [term w (hL w (by simp)) k, ih (fun x hx => hL x (by simp [hx]))]
    ring

set_option maxHeartbeats 400000000 in
theorem spans : ∀ w ∈ shapes, w.2.1 ≤ 6 ∧ w.2.2.1 ≤ 6 ∧ w.2.2.2 ≤ 6 := by
  have h : shapes.all (fun w => decide (w.2.1 ≤ 6 ∧ w.2.2.1 ≤ 6 ∧ w.2.2.2 ≤ 6)) = true := by decide +kernel
  intro w hw
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

theorem rec2 (k : ℕ) : sequence (k+10) = 4*sequence (k+9) - 6*sequence (k+8) + 4*sequence (k+7) - sequence (k+6) := lsum shapes spans k

end P187168

set_option maxHeartbeats 400000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a187168.main := by
  refine ⟨fun n => ?_, P187168.rec2⟩
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> decide +kernel
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have hr := P187168.rec2 k
    have hz : numerator (k + 10) = 0 := by
      unfold numerator
      split_ifs <;> first | omega | rfl
    simp only [lag, show 0 ≤ k + 10 by omega, show 1 ≤ k + 10 by omega, show 2 ≤ k + 10 by omega, show 3 ≤ k + 10 by omega, show 4 ≤ k + 10 by omega, if_true, Nat.sub_zero, show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega, show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega]
    rw [hz]
    linarith
