import OMAStatements.S_oeis_a257838
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open OMA.S_oeis_a257838

namespace FibonacciDiagonal

def fib (j : ℕ) : ℤ := Nat.fib j
def binom (a b : ℕ) : ℤ := a.choose b

lemma fib_next (j : ℕ) : fib (j+2) = fib j + fib (j+1) := by
  simpa [fib] using congrArg (fun a : ℕ => (a : ℤ)) (Nat.fib_add_two (n := j))

lemma pascal (a b : ℕ) : binom (a+1) (b+1) = binom a b + binom a (b+1) := by
  simp [binom, Nat.choose_succ_succ']

lemma step (r j : ℕ) :
    partialSums (r+1) (j+1) = partialSums (r+1) j + partialSums r (j+1) := by
  rw [partialSums, Finset.sum_range_succ, partialSums]

lemma first_row (j : ℕ) : partialSums 1 j = fib (j+2)-1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [step 0 j, ih]
    change fib (j+2)-1+fib (j+1) = fib (j+1+2)-1
    linear_combination -(fib_next (j+1))

lemma second_row (j : ℕ) : partialSums 2 j = fib (j+4)-(j:ℤ)-3 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [step 1 j, ih, first_row]
    push_cast
    linear_combination -(fib_next (j+3))

lemma first_columns (r : ℕ) :
    partialSums r 0 = 0 ∧ partialSums r 1 = 1 ∧ partialSums r 2 = (r:ℤ)+1 := by
  induction r with
  | zero => decide
  | succ r ih =>
    have h0 : partialSums (r+1) 0 = 0 := by simp [partialSums, ih.1]
    have h1 := step r 0
    have h2 := step r 1
    simp only [zero_add, Nat.reduceAdd] at h1 h2
    push_cast
    omega

def residual (r j : ℕ) : ℤ :=
  partialSums (r+2) (j+2) - 4*partialSums (r+1) (j+1) - partialSums r j

def correction (r j : ℕ) : ℤ :=
  binom (r+j+2) (r+1) - 3*binom (r+j+1) (r+1) + binom (r+j) (r+1)

lemma residual_step (r j : ℕ) :
    residual (r+1) (j+1) = residual (r+1) j + residual r (j+1) := by
  unfold residual
  linear_combination (step (r+2) (j+2)) - 4*(step (r+1) (j+1)) - step r j

lemma correction_step (r j : ℕ) :
    correction (r+1) (j+1) = correction (r+1) j + correction r (j+1) := by
  simp only [correction, Nat.succ_add, Nat.add_succ]
  linear_combination (pascal (r+j+3) (r+1)) - 3*(pascal (r+j+2) (r+1)) +
    pascal (r+j+1) (r+1)

lemma array_identity (r j : ℕ) : residual r j = correction r j := by
  induction r generalizing j with
  | zero =>
    simp only [residual, correction, Nat.zero_add, second_row, first_row,
      binom, Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    change fib (j+2+4) - ((j:ℤ)+2) - 3 - 4 * (fib (j+1+2) - 1) - fib j =
      (j:ℤ)+2-3*((j:ℤ)+1)+j
    linarith only [fib_next j, fib_next (j+1), fib_next (j+2), fib_next (j+3), fib_next (j+4)]
  | succ r ih =>
    induction j with
    | zero =>
      simp only [residual, correction, Nat.add_zero, Nat.zero_add,
        (first_columns (r+1+2)).2.2, (first_columns (r+1+1)).2.1,
        (first_columns (r+1)).1, binom, Nat.choose_succ_self_right, Nat.choose_self,
        Nat.choose_succ_self, Nat.cast_succ, Nat.cast_zero]
      ring
    | succ j hj => rw [residual_step, correction_step, hj, ih]

lemma diagonal_identity (n : ℕ) :
    diagonal (n+2) - 4*diagonal (n+1) - diagonal n = -binom (2*n+1) (n+2) := by
  change residual (n+1) n = _
  rw [array_identity]
  simp only [correction, show n+1+n = 2*n+1 by omega]
  have symm : binom (2*n+1) n = binom (2*n+1) (n+1) := by
    unfold binom
    rw [Nat.choose_symm_half]
  linear_combination (pascal (2*n+2) (n+1)) + pascal (2*n+1) n -
    2 * (pascal (2*n+1) (n+1)) + symm

lemma binomial_step (n : ℕ) :
    (n:ℤ)*(n+3)*binom (2*(n+1)+1) (n+1+2) =
      (2*(n:ℤ)+3)*(2*n+2)*binom (2*n+1) (n+2) := by
  have h1 := congrArg (fun a : ℕ => (a:ℤ)) (Nat.add_one_mul_choose_eq (2*n+1) (n+2))
  have h2 := congrArg (fun a : ℕ => (a:ℤ)) (Nat.choose_mul_succ_eq (2*n+2) (n+3))
  rw [show 2*n+2+1-(n+3) = n by omega] at h2
  rw [show 2*(n+1)+1 = 2*n+3 by omega]
  unfold binom
  push_cast at h1 h2
  linear_combination -(2*(n:ℤ)+3) * h1 - ((n:ℤ)+3) * h2

end FibonacciDiagonal

open FibonacciDiagonal

theorem OMA.solution : type_of% @OMA.S_oeis_a257838.main := by
  intro t
  dsimp only
  linear_combination (t:ℤ)*(t+3)*diagonal_identity (t+1) -
    (2*(t:ℤ)+3)*(2*t+2)*diagonal_identity t - binomial_step t
