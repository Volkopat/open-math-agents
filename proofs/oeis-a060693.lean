import OMAStatements.S_oeis_a060693
import Mathlib

open OMA.S_oeis_a060693
open Finset

namespace P060693

theorem dvd_aux (n j : ℕ) (hj : j ≤ n) : (j + 1) ∣ n.choose j * (n + j).choose n := by
  have h1 : (n + j).choose (2 * j) * (2 * j).choose j =
      (n + j).choose j * (n + j - j).choose (2 * j - j) := Nat.choose_mul (by omega)
  rw [show n + j - j = n by omega, show 2 * j - j = j by omega] at h1
  have h2 : (n + j).choose j = (n + j).choose n := Nat.choose_symm_of_eq_add (by ring)
  rw [mul_comm, ← h2, ← h1, ← Nat.centralBinom_eq_two_mul_choose]
  exact Dvd.dvd.mul_left (Nat.succ_dvd_centralBinom j) _

theorem term (n k : ℕ) (hk : k ≤ n) :
    (-1 : ℤ) ^ k * ((Nat.choose n k * Nat.choose (2 * n - k) n / (n + 1 - k) : ℕ) : ℤ) *
      ((n + 1 - k : ℕ) : ℤ) ^ 2 =
    (-1 : ℤ) ^ k * ((Nat.choose n k * Nat.choose (2 * n - k) n : ℕ) : ℤ) * ((n + 1 - k : ℕ) : ℤ) := by
  have hd : (n + 1 - k) ∣ Nat.choose n k * Nat.choose (2 * n - k) n := by
    have := dvd_aux n (n - k) (by omega)
    rwa [show n - k + 1 = n + 1 - k by omega, Nat.choose_symm hk, show n + (n - k) = 2 * n - k by omega] at this
  have e := Nat.div_mul_cancel hd
  rw [sq, ← mul_assoc, mul_assoc ((-1 : ℤ) ^ k), ← Nat.cast_mul, e]

theorem R_eq (n j : ℕ) : (((n + j).choose n : ℕ) : ℤ) * ((j : ℤ) + 1) =
    ((n : ℤ) + 1) * (((j + (n + 1)).choose (n + 1) : ℕ) : ℤ) - (n : ℤ) * (((j + n).choose n : ℕ) : ℤ) := by
  have h := Nat.add_one_mul_choose_eq (j + n) n
  rw [show j + n + 1 = j + (n + 1) by ring] at h
  have h' : (((j + n + 1 : ℕ) : ℤ)) * (((j + n).choose n : ℕ) : ℤ) =
      (((j + (n + 1)).choose (n + 1) : ℕ) : ℤ) * ((n : ℤ) + 1) := by exact_mod_cast h
  rw [show n + j = j + n by ring]
  push_cast at h' ⊢
  linear_combination h'

theorem sumF (n : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * f k = (fwdDiff 1)^[n] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [smul_eq_mul]

theorem key (n : ℕ) :
    ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * ((((n + j).choose n : ℕ) : ℤ) * ((j : ℤ) + 1)) =
      1 + n + n ^ 2 := by
  simp only [R_eq, mul_sub]
  rw [Finset.sum_sub_distrib]
  have e1 : ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) *
      (((n : ℤ) + 1) * (((j + (n + 1)).choose (n + 1) : ℕ) : ℤ)) =
      ((n : ℤ) + 1) * ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) *
        (fun r => (((r + (n + 1)).choose (n + 1) : ℕ) : ℤ)) j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have e2 : ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) *
      ((n : ℤ) * (((j + n).choose n : ℕ) : ℤ)) =
      (n : ℤ) * ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) *
        (fun r => (((r + n).choose n : ℕ) : ℤ)) j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [e1, e2, sumF, sumF]
  rw [fwdDiff_iter_comp_add 1 (fun x => ((x.choose (n + 1) : ℕ) : ℤ)) (n + 1) n 0,
    fwdDiff_iter_comp_add 1 (fun x => ((x.choose n : ℕ) : ℤ)) n n 0]
  have c1 := fwdDiff_iter_choose 1 n
  have c0 := fwdDiff_iter_choose 0 n
  rw [add_zero] at c0
  rw [c1, c0]
  simp
  ring

end P060693

theorem OMA.solution : type_of% @OMA.S_oeis_a060693.main := by
  intro n
  rw [Finset.sum_congr rfl fun k hk => P060693.term n k (by simp at hk; omega)]
  rw [← Finset.sum_range_reflect]
  rw [← P060693.key n]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [show n + 1 - 1 - j = n - j by omega, show 2 * n - (n - j) = n + j by omega,
    show n + 1 - (n - j) = j + 1 by omega, Nat.choose_symm (by omega : j ≤ n)]
  push_cast
  ring
