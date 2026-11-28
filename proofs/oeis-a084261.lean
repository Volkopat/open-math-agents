import OMAStatements.S_oeis_a084261
import Mathlib
open OMA.S_oeis_a084261

namespace OMA.P_oeis_a084261
theorem tr_succ (n : ℕ) (f : ℕ → ℤ) :
    transform (n + 1) f = transform n f + transform n (fun j => f (j + 1)) := by
  unfold transform
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun j => ((n.choose (j+1) : ℕ) : ℤ) * f (j + 1)),
    Nat.choose_succ_self, Finset.sum_range_succ' (fun j => ((n.choose j : ℕ) : ℤ) * f j)]
  simp
  ring

theorem tr_mul (k : ℕ) (f : ℕ → ℤ) :
    ((k : ℤ) + 1) * transform k (fun j => f (j + 1))
      = transform (k + 1) (fun i => (i : ℤ) * f i) := by
  unfold transform
  rw [Finset.sum_range_succ' _ (k + 1), Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h := Nat.add_one_mul_choose_eq k j
  have h' : ((k : ℤ) + 1) * (k.choose j : ℤ) = ((k+1).choose (j+1) : ℤ) * ((j : ℤ) + 1) := by
    exact_mod_cast h
  push_cast
  linear_combination f (j + 1) * h'

theorem interlaced_rec (j : ℕ) :
    2 * interlaced (j + 2) - ((j : ℤ) + 2) * interlaced j = 0 := by
  unfold interlaced
  have h2 : (j + 2) % 2 = j % 2 := by omega
  rw [h2]
  split_ifs with h
  · have h3 : (j + 2) / 2 = j / 2 + 1 := by omega
    rw [h3, Nat.factorial_succ]
    have h4 : ((j : ℤ) + 2) = 2 * ((j / 2 : ℕ) + 1 : ℕ) := by push_cast; omega
    rw [h4]; push_cast; ring
  · ring

end OMA.P_oeis_a084261

open OMA.P_oeis_a084261 in
theorem OMA.solution : type_of% @OMA.S_oeis_a084261.main := by
  intro k
  unfold a
  have e1 := tr_succ k interlaced
  have e2 := tr_succ (k + 1) interlaced
  have e3 := tr_succ (k + 2) interlaced
  have e4 := tr_succ (k + 1) (fun j => interlaced (j + 1))
  have e5 := tr_mul k (fun j => interlaced j)
  have key : ((k : ℤ) + 1) * a (k + 1) - ((k : ℤ) + 1) * a k
      = transform (k + 1) (fun i => (i : ℤ) * interlaced i) := by
    unfold a; rw [← e5, e1]; ring
  unfold a at key
  rw [show k + 3 = (k + 2) + 1 by rfl, e3, show k + 2 = (k + 1) + 1 by rfl, e2, e4]
  have : 2 * (transform (k + 1) interlaced + transform (k + 1) (fun j => interlaced (j + 1)) +
      (transform (k + 1) (fun j => interlaced (j + 1)) +
        transform (k + 1) (fun j => interlaced (j + 1 + 1)))) -
      4 * (transform (k + 1) interlaced + transform (k + 1) (fun j => interlaced (j + 1)))
      - transform (k + 1) (fun i => (i : ℤ) * interlaced i) = 0 := by
    unfold transform
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have := interlaced_rec j
    linear_combination ((k+1).choose j : ℤ) * this
  linear_combination this - key
