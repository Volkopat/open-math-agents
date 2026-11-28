import OMAStatements.S_oeis_a187167
import Mathlib

open OMA.S_oeis_a187167

namespace P187167

theorem term (w : Profile) (h : w.2.1 ≤ 5 ∧ w.2.2.1 ≤ 5 ∧ w.2.2.2 ≤ 5) (k : ℕ) :
    placed (k+9) w = 4*placed (k+8) w - 6*placed (k+7) w + 4*placed (k+6) w - placed (k+5) w := by
  obtain ⟨c, a, b, e⟩ := w
  obtain ⟨ha, hb, he⟩ := h
  simp only at ha hb he
  simp only [placed, Nat.cast_sub (show a ≤ k + 5 by omega), Nat.cast_sub (show a ≤ k + 6 by omega), Nat.cast_sub (show a ≤ k + 7 by omega), Nat.cast_sub (show a ≤ k + 8 by omega), Nat.cast_sub (show a ≤ k + 9 by omega), Nat.cast_sub (show b ≤ k + 5 by omega), Nat.cast_sub (show b ≤ k + 6 by omega), Nat.cast_sub (show b ≤ k + 7 by omega), Nat.cast_sub (show b ≤ k + 8 by omega), Nat.cast_sub (show b ≤ k + 9 by omega), Nat.cast_sub (show e ≤ k + 5 by omega), Nat.cast_sub (show e ≤ k + 6 by omega), Nat.cast_sub (show e ≤ k + 7 by omega), Nat.cast_sub (show e ≤ k + 8 by omega), Nat.cast_sub (show e ≤ k + 9 by omega)]
  push_cast
  ring

theorem lsum (L : List Profile) (hL : ∀ w ∈ L, w.2.1 ≤ 5 ∧ w.2.2.1 ≤ 5 ∧ w.2.2.2 ≤ 5) (k : ℕ) :
    (L.map (placed (k+9))).sum = 4*(L.map (placed (k+8))).sum - 6*(L.map (placed (k+7))).sum + 4*(L.map (placed (k+6))).sum - (L.map (placed (k+5))).sum := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [term w (hL w (by simp)) k, ih (fun x hx => hL x (by simp [hx]))]
    ring

set_option maxHeartbeats 400000000 in
theorem spans : ∀ w ∈ shapes, w.2.1 ≤ 5 ∧ w.2.2.1 ≤ 5 ∧ w.2.2.2 ≤ 5 := by
  have h : shapes.all (fun w => decide (w.2.1 ≤ 5 ∧ w.2.2.1 ≤ 5 ∧ w.2.2.2 ≤ 5)) = true := by decide +kernel
  intro w hw
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

theorem rec2 (k : ℕ) : sequence (k+9) = 4*sequence (k+8) - 6*sequence (k+7) + 4*sequence (k+6) - sequence (k+5) := lsum shapes spans k

end P187167

set_option maxHeartbeats 400000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a187167.main := by
  refine ⟨fun n => ?_, P187167.rec2⟩
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> decide +kernel
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have hr := P187167.rec2 k
    have hz : numerator (k + 9) = 0 := by
      unfold numerator
      split_ifs <;> first | omega | rfl
    simp only [lag, show 0 ≤ k + 9 by omega, show 1 ≤ k + 9 by omega, show 2 ≤ k + 9 by omega, show 3 ≤ k + 9 by omega, show 4 ≤ k + 9 by omega, if_true, Nat.sub_zero, show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega]
    rw [hz]
    linarith
