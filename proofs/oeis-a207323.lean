import OMAStatements.S_oeis_a207323
import Mathlib

open OMA.S_oeis_a207323

private def Pc (n k : ℚ) : ℚ := (8) * n ^ 0 * k ^ 3 + (-3) * n ^ 0 * k ^ 4 + (20) * n ^ 1 * k ^ 3 + (-6) * n ^ 1 * k ^ 4 + (16) * n ^ 2 * k ^ 3 + (-3) * n ^ 2 * k ^ 4 + (4) * n ^ 3 * k ^ 3

private def H (n k : ℕ) : ℚ := Pc n k * ((n + 2).choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ) /
  (((n : ℚ) + 1) * ((n : ℚ) + 2)) ^ 2

private lemma c1 (n k : ℕ) (hk : k ≤ n + 2) :
    ((n + 1).choose k : ℚ) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) / ((n : ℚ) + 2) := by
  have h := Nat.choose_mul_succ_eq (n + 1) k
  have h' : ((n + 1).choose k : ℚ) * ((n : ℚ) + 2) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) := by
    have : ((n + 1 + 1 - k : ℕ) : ℚ) = (n : ℚ) + 2 - k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this]; exact_mod_cast h
  have : ((n : ℚ) + 2) ≠ 0 := by positivity
  field_simp; linarith

private lemma c0 (n k : ℕ) (hk : k ≤ n + 2) :
    (n.choose k : ℚ) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) * ((n : ℚ) + 1 - k) /
      (((n : ℚ) + 1) * ((n : ℚ) + 2)) := by
  rcases Nat.lt_or_ge (n + 1) k with h | h
  · have hk2 : k = n + 2 := by omega
    subst hk2
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    push_cast; ring
  · have h1 := Nat.choose_mul_succ_eq n k
    have h' : (n.choose k : ℚ) * ((n : ℚ) + 1) = ((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - k) := by
      have : ((n + 1 - k : ℕ) : ℚ) = (n : ℚ) + 1 - k := by
        rw [Nat.cast_sub h]; push_cast; ring
      rw [← this]; exact_mod_cast h1
    rw [c1 n k hk] at h'
    have : ((n : ℚ) + 1) ≠ 0 := by positivity
    have : ((n : ℚ) + 2) ≠ 0 := by positivity
    field_simp at h' ⊢; linear_combination h'

private lemma cs (n k : ℕ) (hk : k ≤ n + 2) :
    ((n + 2).choose (k + 1) : ℚ) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) / ((k : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq (n + 2) k
  have h' : ((n + 2).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) := by
    have : ((n + 2 - k : ℕ) : ℚ) = (n : ℚ) + 2 - k := by
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [← this]; exact_mod_cast h
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

private lemma cb (k : ℕ) : ((2 * (k + 1)).choose (k + 1) : ℚ) = ((2 * k).choose k : ℚ) * (4 * k + 2) / (k + 1) := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((k : ℚ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℚ) = 2 * (2 * k + 1) * ((2 * k).choose k : ℚ) := by
    exact_mod_cast h
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

private lemma term (n k : ℕ) (hk : k ≤ n + 2) :
    -9 * ((n : ℚ) + 1) ^ 2 * ((n.choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ))
      + (10 * (n : ℚ) ^ 2 + 30 * n + 23) * (((n + 1).choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ))
      - ((n : ℚ) + 2) ^ 2 * (((n + 2).choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ)) = H n (k + 1) - H n k := by
  unfold H
  rw [cs n k hk, c0 n k hk, c1 n k hk, cb k]
  have : ((n : ℚ) + 1) ≠ 0 := by positivity
  have : ((n : ℚ) + 2) ≠ 0 := by positivity
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  unfold Pc
  push_cast
  field_simp
  ring

private lemma ext_sum (n e : ℕ) : (A002893 n : ℚ) =
    ∑ k ∈ Finset.range (n + 1 + e), ((n.choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ)) := by
  induction e with
  | zero => unfold A002893; push_cast; rfl
  | succ e ih =>
    rw [← add_assoc, Finset.sum_range_succ, ← ih, Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma hrec (n : ℕ) : ((n : ℚ) + 2) ^ 2 * A002893 (n + 2) =
    (10 * (n : ℚ) ^ 2 + 30 * n + 23) * A002893 (n + 1) - 9 * ((n : ℚ) + 1) ^ 2 * A002893 n := by
  have htel := Finset.sum_range_sub (H n) (n + 3)
  have hsum : ∑ k ∈ Finset.range (n + 3), (-9 * ((n : ℚ) + 1) ^ 2 * ((n.choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ))
      + (10 * (n : ℚ) ^ 2 + 30 * n + 23) * (((n + 1).choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ))
      - ((n : ℚ) + 2) ^ 2 * (((n + 2).choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ))) = H n (n + 3) - H n 0 := by
    rw [← htel]
    exact Finset.sum_congr rfl (fun k hk => term n k (by simp at hk; omega))
  have h0 : H n 0 = 0 := by simp [H, Pc]
  have h3 : H n (n + 3) = 0 := by simp [H, Nat.choose_eq_zero_of_lt (show n + 2 < n + 3 by omega)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, h0, h3] at hsum
  rw [ext_sum n 2, ext_sum (n + 1) 1, ext_sum (n + 2) 0]
  rw [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 + 1 = n + 3 by omega,
    show n + 2 + 1 + 0 = n + 3 by omega]
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a207323.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
    show m + 4 - 4 = m by omega]
  have r1 := hrec (m + 1)
  have r2 := hrec (m + 2)
  rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at r1
  rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at r2
  push_cast at r1 r2
  have e1 : a (m + 1) = a m + ((m : ℤ) + 1) * A002893 (m + 1) := by simp [a, Finset.sum_range_succ (n := m + 1)]
  have e2 : a (m + 2) = a (m + 1) + ((m : ℤ) + 2) * A002893 (m + 2) := by
    simp [a, Finset.sum_range_succ (n := m + 2)]
  have e3 : a (m + 3) = a (m + 2) + ((m : ℤ) + 3) * A002893 (m + 3) := by
    simp [a, Finset.sum_range_succ (n := m + 3)]
  have e4 : a (m + 4) = a (m + 3) + ((m : ℤ) + 4) * A002893 (m + 4) := by
    simp [a, Finset.sum_range_succ (n := m + 4)]
  rw [e4, e3, e2, e1]
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination ((m : ℚ) + 3) * r2 - 3 * ((m : ℚ) + 1) * r1
