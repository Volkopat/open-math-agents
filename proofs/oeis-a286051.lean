import OMAStatements.S_oeis_a286051
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Digits.Defs

open OMA.S_oeis_a286051

namespace OMA.A286051

private theorem inputPair (k : ℕ) :
    (tm (2*k) = 0 ∧ tm (2*k+1) = 1) ∨ (tm (2*k) = 1 ∧ tm (2*k+1) = 0) := by
  have oddDigits : Nat.digits 2 (2*k+1) = 1 :: Nat.digits 2 k := by
    simpa only [Nat.add_comm (2*k) 1] using
      (Nat.digits_add 2 (by decide) 1 k (by decide) (Or.inl (by decide)))
  by_cases hk : k = 0
  · subst k
    decide
  have evenDigits : Nat.digits 2 (2*k) = 0 :: Nat.digits 2 k := by
    simpa only [Nat.zero_add] using
      (Nat.digits_add 2 (by decide) 0 k (by decide) (Or.inr hk))
  simp only [tm, oddDigits, evenDigits]
  simp only [List.count_cons, beq_self_eq_true, Bool.false_eq_true,
    if_true, if_false, Nat.reduceBEq, Nat.add_zero]
  omega

private theorem scanPair (k : ℕ) (h : ∃ j, pos (2*k) = 2*j) :
    ((w (2*k) = 0 ∧ w (2*k+1) = 1) ∨ (w (2*k) = 1 ∧ w (2*k+1) = 0)) ∧
      ∃ j, pos (2*(k+1)) = 2*j := by
  obtain ⟨j, hj⟩ := h
  have step : pos (2*k+1) = 2*j+1 := by
    rw [pos, hj]
    rcases inputPair j with h | h <;> simp [h.1, h.2]
  constructor
  · simpa only [w, hj, step] using inputPair j
  · rw [show 2*(k+1) = (2*k+1)+1 by omega, pos, step]
    split
    · exact ⟨j+2, by omega⟩
    · exact ⟨j+1, by omega⟩

private theorem aligned (k : ℕ) : ∃ j, pos (2*k) = 2*j := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih => exact (scanPair k ih).2

private theorem pairsCount (k : ℕ) : Nat.count (fun i => w i = 1) (2*k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega, Nat.count_succ, Nat.count_succ, ih]
    rcases (scanPair k (aligned k)).1 with h | h <;> simp [h.1, h.2]

end OMA.A286051

theorem OMA.solution : type_of% @OMA.S_oeis_a286051.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have c := OMA.A286051.pairsCount k
  rcases (OMA.A286051.scanPair k (OMA.A286051.aligned k)).1 with h | h
  · have c' : Nat.count (fun i => w i = 1) (2*k+1) = k := by
      rw [Nat.count_succ, c]
      simp [h.1]
    have e := Nat.nth_count (p := fun i => w i = 1) (n := 2*k+1) h.2
    rw [c'] at e
    left
    simp only [a, Nat.succ_sub_one, e, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_succ]
    omega
  · have e := Nat.nth_count (p := fun i => w i = 1) (n := 2*k) h.1
    rw [c] at e
    right
    simp only [a, Nat.succ_sub_one, e, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_succ]
    omega
