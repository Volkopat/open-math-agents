import OMAStatements.S_oeis_a259914
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open OMA.S_oeis_a259914

namespace SteppedCubesProof

def closed (r j : ℕ) : ℚ := (6*(j : ℚ)^2+6*j*r+12*j+(r+3)*(r+2))*((j+r+1).factorial : ℚ) /
    (((r+3).factorial : ℚ)*(j.factorial : ℚ))

lemma closed_form (r j : ℕ) : partialSums r j = closed r j := by
  induction r generalizing j with
  | zero =>
    simp [partialSums, closed, Nat.factorial_succ]
    field_simp <;> ring
  | succ r ih =>
    induction j with
    | zero =>
      simp only [partialSums, Finset.range_one, Finset.sum_singleton, ih, closed,
        Nat.zero_add, Nat.factorial_succ, Nat.factorial_zero, Nat.cast_zero,
        Nat.cast_mul, Nat.cast_succ]
      field_simp
      ring
    | succ j hj =>
      have step : partialSums (r+1) (j+1) = partialSums (r+1) j + partialSums r (j+1) := by
        rw [partialSums, Finset.sum_range_succ, partialSums]
      rw [step, hj, ih]
      simp only [closed, Nat.succ_add, Nat.add_succ, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_succ, Nat.cast_add]
      field_simp
      ring

def oddTerm (k : ℕ) : ℚ := (13*(k : ℚ)^2+25*k+12)*((2*k+2).factorial : ℚ) /
    (((k+4).factorial : ℚ)*(k.factorial : ℚ))

def evenTerm (k : ℕ) : ℚ := (13*(k : ℚ)^2+43*k+36)*((2*k+3).factorial : ℚ) /
    (((k+4).factorial : ℚ)*((k+1).factorial : ℚ))

lemma odd_path (k : ℕ) : path (2*k) = oddTerm k := by
  unfold path
  rw [show 2*k/2 = k by omega, show (2*k+1)/2 = k by omega, closed_form]
  unfold closed oddTerm
  rw [show k+(k+1)+1 = 2*k+2 by omega]
  push_cast
  ring

lemma even_path (k : ℕ) : path (2*k+1) = evenTerm k := by
  unfold path
  rw [show (2*k+1)/2 = k by omega, show (2*k+1+1)/2 = k+1 by omega, closed_form]
  unfold closed evenTerm
  rw [show (k+1)+(k+1)+1 = 2*k+3 by omega]
  push_cast
  ring

end SteppedCubesProof

open SteppedCubesProof

set_option maxHeartbeats 2500000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a259914.main := by
  intro t
  dsimp only
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2*k ∨ t = 2*k+1 := ⟨t/2, by omega⟩
  rw [show 2*k+3 = 2*(k+1)+1 by omega, even_path,
      show 2*k+2 = 2*(k+1) by omega, odd_path, even_path, odd_path]
  pick_goal 2
  rw [show 2*k+1+3 = 2*(k+2) by omega, odd_path,
      show 2*k+1+2 = 2*(k+1)+1 by omega, even_path,
      show 2*k+1+1 = 2*(k+1) by omega, odd_path, even_path]
  all_goals
    simp only [oddTerm, evenTerm, Nat.mul_add, Nat.mul_one, Nat.reduceMul, Nat.add_assoc,
      Nat.reduceAdd, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    field_simp
    ring
