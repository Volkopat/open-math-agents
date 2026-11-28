import OMAStatements.S_oeis_a181270
import Mathlib

open OMA.S_oeis_a181270

namespace P181270

theorem hs (n : ℕ) (a b c : Bool) : afterFirst (n + 1) a b c = afterFirst n a b c +
    afterFirst n a b (!c) + afterFirst n (!a) b c + afterFirst n (!a) (!b) (!c) := rfl

theorem hb (n : ℕ) (p : Bool) : beforeFirst (n + 1) p =
    beforeFirst n p + afterFirst n p p (!p) + beforeFirst n (!p) := rfl

theorem G : ∀ k : ℕ, ∀ a b c : Bool, afterFirst (k + 4) a b c =
    4 * afterFirst (k + 3) a b c + 4 * afterFirst (k + 2) a b c - 16 * afterFirst (k + 1) a b c := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    intro a b c
    show afterFirst (k + 5) a b c = 4 * afterFirst (k + 4) a b c + 4 * afterFirst (k + 3) a b c - 16 * afterFirst (k + 2) a b c
    have s5 : afterFirst (k + 5) a b c = afterFirst (k + 4) a b c + afterFirst (k + 4) a b (!c) + afterFirst (k + 4) (!a) b c + afterFirst (k + 4) (!a) (!b) (!c) := rfl
    have s4 : afterFirst (k + 4) a b c = afterFirst (k + 3) a b c + afterFirst (k + 3) a b (!c) + afterFirst (k + 3) (!a) b c + afterFirst (k + 3) (!a) (!b) (!c) := rfl
    have s3 : afterFirst (k + 3) a b c = afterFirst (k + 2) a b c + afterFirst (k + 2) a b (!c) + afterFirst (k + 2) (!a) b c + afterFirst (k + 2) (!a) (!b) (!c) := rfl
    have s2 : afterFirst (k + 2) a b c = afterFirst (k + 1) a b c + afterFirst (k + 1) a b (!c) + afterFirst (k + 1) (!a) b c + afterFirst (k + 1) (!a) (!b) (!c) := rfl
    have e1 := ih a b c
    have e2 := ih a b (!c)
    have e3 := ih (!a) b c
    have e4 := ih (!a) (!b) (!c)
    linear_combination s5 - 4 * s4 - 4 * s3 + 16 * s2 + e1 + e2 + e3 + e4

theorem H : ∀ k : ℕ, ∀ p : Bool, beforeFirst (k + 5) p =
    4 * beforeFirst (k + 4) p + 4 * beforeFirst (k + 3) p - 16 * beforeFirst (k + 2) p := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    intro p
    show beforeFirst (k + 6) p = 4 * beforeFirst (k + 5) p + 4 * beforeFirst (k + 4) p - 16 * beforeFirst (k + 3) p
    have t6 : beforeFirst (k + 6) p = beforeFirst (k + 5) p + afterFirst (k + 5) p p (!p) + beforeFirst (k + 5) (!p) := rfl
    have t5 : beforeFirst (k + 5) p = beforeFirst (k + 4) p + afterFirst (k + 4) p p (!p) + beforeFirst (k + 4) (!p) := rfl
    have t4 : beforeFirst (k + 4) p = beforeFirst (k + 3) p + afterFirst (k + 3) p p (!p) + beforeFirst (k + 3) (!p) := rfl
    have t3 : beforeFirst (k + 3) p = beforeFirst (k + 2) p + afterFirst (k + 2) p p (!p) + beforeFirst (k + 2) (!p) := rfl
    have e1 := ih p
    have e2 := ih (!p)
    have e3 := G (k + 1) p p (!p)
    linear_combination t6 - 4 * t5 - 4 * t4 + 16 * t3 + e1 + e2 + e3

end P181270

theorem OMA.solution : type_of% @OMA.S_oeis_a181270.main := by
  refine ⟨fun n => ?_, fun k => P181270.H k false⟩
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    have hr := P181270.H k false
    have hz : numerator (k + 5) = 0 := by
      unfold numerator
      split_ifs <;> first | omega | rfl
    simp only [lag, show 0 ≤ k + 5 by omega, show 1 ≤ k + 5 by omega, show 2 ≤ k + 5 by omega,
      show 3 ≤ k + 5 by omega, if_true, Nat.sub_zero, show k + 5 - 1 = k + 4 by omega,
      show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega]
    rw [hz]
    simp only [OMA.S_oeis_a181270.sequence]
    linarith
