import OMAStatements.S_oeis_a340507
import Mathlib

open OMA.S_oeis_a340507

namespace P340507

theorem core (x y : ℕ) :
    |variantX (x : ℤ) (y : ℤ) - originalX (x : ℤ) (y : ℤ)| = if x < y then 1 else 0 := by
  simp only [variantX, originalX]
  split_ifs <;>
  first
  | (rw [abs_eq_zero]; omega)
  | (rw [abs_eq (by norm_num)]; omega)

theorem sq (r y : ℕ) (hy : y ≤ r) :
    (r * (r + 1) + 2 * y).sqrt = if r - y < y then r + 1 else r := by
  split_ifs with h
  · have h' : r + 1 ≤ 2 * y := by omega
    symm; rw [Nat.eq_sqrt]; constructor <;> nlinarith
  · have h' : 2 * y ≤ r := by omega
    symm; rw [Nat.eq_sqrt]; constructor <;> nlinarith

theorem rowb (n : ℕ) : row n * (row n + 1) ≤ 2 * n ∧ 2 * n < (row n + 1) * (row n + 2) := by
  have h1 := Nat.sqrt_le' (8 * n + 1)
  have h2 := Nat.lt_succ_sqrt' (8 * n + 1)
  have hs : 1 ≤ (8 * n + 1).sqrt := Nat.le_sqrt.mpr (by omega)
  unfold row
  set s := (8 * n + 1).sqrt
  have e1 : 2 * ((s - 1) / 2) + 1 ≤ s := by omega
  have e2 : s ≤ 2 * ((s - 1) / 2) + 2 := by omega
  set r := (s - 1) / 2
  constructor <;> nlinarith

end P340507

theorem OMA.solution : type_of% @OMA.S_oeis_a340507.main := by
  intro n
  obtain ⟨b1, b2⟩ := P340507.rowb n
  have hev : 2 ∣ row n * (row n + 1) := (Nat.even_mul_succ_self (row n)).two_dvd
  have hT : row n * (row n + 1) / 2 * 2 = row n * (row n + 1) := Nat.div_mul_cancel hev
  have e3 : (row n + 1) * (row n + 2) = row n * (row n + 1) + 2 * (row n + 1) := by ring
  have hy : pointY n ≤ row n := by unfold pointY; omega
  have h2n : 2 * n = row n * (row n + 1) + 2 * pointY n := by unfold pointY; omega
  have hx : pointX n = row n - pointY n := rfl
  unfold difference
  rw [hx, P340507.core, h2n, P340507.sq _ _ hy]
  split_ifs <;> push_cast <;> ring
