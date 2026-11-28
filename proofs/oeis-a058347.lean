import OMAStatements.S_oeis_a058347
import Mathlib

/-! Normalizing by the number of binary matrices gives a weighted recurrence.
The transposed recurrence follows from the same recurrence on the four
neighboring cells and the boundary values. -/
namespace Deldor14.DoubleSupport
open OMA.S_oeis_a058347
private def S (n k : ℕ) : ℚ := (T n k : ℚ) / (2:ℚ)^(n*k)
private def q (n : ℕ) : ℚ := ((2:ℚ)^n)⁻¹
private def F (n k : ℕ) : ℚ :=
  2*(1-q k) + 2*((k:ℚ)-2)*q n + 4*q n*q k + 2*((n:ℚ)-1)*q k*(1-q k)
private theorem q_succ (n : ℕ) : q (n+1)=q n/2 := by
  simp [q,pow_succ,div_eq_mul_inv,mul_comm]
private theorem zero_row (n : ℕ) : S 0 n=0 := by simp [S,T]
private theorem zero_col (n : ℕ) : S n 0=0 := by
  cases n with
  | zero => exact zero_row _
  | succ n => cases n <;> simp [S,T]
private theorem one_row (n : ℕ) : S 1 n=n := by
  cases n with
  | zero => simp [zero_col]
  | succ n => simp [S,T]
private theorem first (n : ℕ) : T n 1 = n*2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [T,ih,pow_succ (2:ℕ) (n+1)]
      ring
private theorem one_col (n : ℕ) : S n 1=n := by simp [S,first]
private theorem vertical (n k : ℕ) :
    S (n+1) (k+1) = q (k+1)*S n (k+1) + (1-q (k+1))*S n k + F (n+1) (k+1) := by
  cases n with
  | zero => simp [one_row,zero_row,F,q];ring
  | succ n =>
    cases k with
    | zero => simp [one_col,zero_col,F,q];ring
    | succ k =>
      have h₁ : 2 ≤ (2:ℕ)^(k+3) := by
        exact le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) (by omega))
      have h₂ : 1 ≤ (2:ℕ)^(k+2) := Nat.one_le_pow _ _ (by decide)
      simp only [S,q,F]
      conv_lhs => rw [T]
      push_cast [Nat.cast_sub h₁,Nat.cast_sub h₂]
      simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.mul_add,pow_add,pow_mul]
      field_simp
      <;> ring

private theorem horizontal (n k : ℕ) :
    S (n+1) (k+1) = q (n+1)*S (n+1) k + (1-q (n+1))*S n k + F (k+1) (n+1) := by
  induction n generalizing k with
  | zero => simp [one_row,zero_row,F,q];ring
  | succ n ih =>
    cases k with
    | zero => simp [one_col,zero_col,F,q];ring
    | succ k =>
      rw [vertical (n+1) (k+1), ih (k+1), vertical (n+1) k]
      have a := vertical n k
      have b := ih k
      simp only [F,q_succ,Nat.cast_succ,Nat.cast_add,Nat.cast_one] at a b ⊢
      linear_combination -((1-q n/2)/2)*a + ((1-q k/2)/2)*b

private theorem symmetry (n k : ℕ) : S n k=S k n := by
  induction n generalizing k with
  | zero => rw [zero_row,zero_col]
  | succ n ih =>
    cases k with
    | zero => rw [zero_col,zero_row]
    | succ k => rw [vertical n k,horizontal k n,ih (k+1),ih k]

end Deldor14.DoubleSupport
open Deldor14.DoubleSupport in
theorem OMA.solution : type_of% @OMA.S_oeis_a058347.main := by
  intro n k
  have h := symmetry n k
  unfold S at h
  rw [Nat.mul_comm k n] at h
  have v := (div_left_inj' (by positivity : (2:ℚ)^(n*k)≠0)).mp h
  exact_mod_cast v
