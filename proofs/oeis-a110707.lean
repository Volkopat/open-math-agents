import OMAStatements.S_oeis_a110707
import Mathlib

open OMA.S_oeis_a110707

namespace P110707

def Pc (n k : ℚ) : ℚ := (72) * n ^ 0 * k ^ 3 + (-78) * n ^ 0 * k ^ 4 + (30) * n ^ 0 * k ^ 5 + (-4) * n ^ 0 * k ^ 6 + (272) * n ^ 1 * k ^ 3 + (-249) * n ^ 1 * k ^ 4 + (78) * n ^ 1 * k ^ 5 + (-8) * n ^ 1 * k ^ 6 + (402) * n ^ 2 * k ^ 3 + (-291) * n ^ 2 * k ^ 4 + (66) * n ^ 2 * k ^ 5 + (-4) * n ^ 2 * k ^ 6 + (290) * n ^ 3 * k ^ 3 + (-147) * n ^ 3 * k ^ 4 + (18) * n ^ 3 * k ^ 5 + (102) * n ^ 4 * k ^ 3 + (-27) * n ^ 4 * k ^ 4 + (14) * n ^ 5 * k ^ 3

def H (n k : ℕ) : ℚ := Pc n k * ((n + 2).choose k : ℚ) ^ 3 / (((n : ℚ) + 1) * ((n : ℚ) + 2)) ^ 3

lemma c1 (n k : ℕ) (hk : k ≤ n + 2) :
    ((n + 1).choose k : ℚ) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) / ((n : ℚ) + 2) := by
  have h := Nat.choose_mul_succ_eq (n + 1) k
  have h' : ((n + 1).choose k : ℚ) * ((n : ℚ) + 2) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) := by
    have : ((n + 1 + 1 - k : ℕ) : ℚ) = (n : ℚ) + 2 - k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this]; exact_mod_cast h
  have : ((n : ℚ) + 2) ≠ 0 := by positivity
  field_simp; linarith

lemma c0 (n k : ℕ) (hk : k ≤ n + 2) :
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

lemma cs (n k : ℕ) (hk : k ≤ n + 2) :
    ((n + 2).choose (k + 1) : ℚ) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) / ((k : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq (n + 2) k
  have h' : ((n + 2).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) := by
    have : ((n + 2 - k : ℕ) : ℚ) = (n : ℚ) + 2 - k := by
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [← this]; exact_mod_cast h
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

lemma term (n k : ℕ) (hk : k ≤ n + 2) :
    8 * ((n : ℚ) + 1) ^ 2 * (n.choose k : ℚ) ^ 3 + (7 * (n : ℚ) ^ 2 + 21 * n + 16) * ((n + 1).choose k : ℚ) ^ 3
      - ((n : ℚ) + 2) ^ 2 * ((n + 2).choose k : ℚ) ^ 3 = H n (k + 1) - H n k := by
  unfold H
  rw [cs n k hk, c0 n k hk, c1 n k hk]
  have : ((n : ℚ) + 1) ≠ 0 := by positivity
  have : ((n : ℚ) + 2) ≠ 0 := by positivity
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  unfold Pc
  push_cast
  field_simp
  ring

lemma ext_sum (n e : ℕ) : (franel n : ℚ) = ∑ k ∈ Finset.range (n + 1 + e), ((n.choose k : ℚ)) ^ 3 := by
  induction e with
  | zero => unfold franel; push_cast; rfl
  | succ e ih =>
    rw [← add_assoc, Finset.sum_range_succ, ← ih, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma frec (n : ℕ) : ((n : ℚ) + 2) ^ 2 * franel (n + 2) =
    (7 * (n : ℚ) ^ 2 + 21 * n + 16) * franel (n + 1) + 8 * ((n : ℚ) + 1) ^ 2 * franel n := by
  have htel := Finset.sum_range_sub (H n) (n + 3)
  have hsum : ∑ k ∈ Finset.range (n + 3), (8 * ((n : ℚ) + 1) ^ 2 * (n.choose k : ℚ) ^ 3
      + (7 * (n : ℚ) ^ 2 + 21 * n + 16) * ((n + 1).choose k : ℚ) ^ 3
      - ((n : ℚ) + 2) ^ 2 * ((n + 2).choose k : ℚ) ^ 3) = H n (n + 3) - H n 0 := by
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

lemma fz (m : ℕ) (x1 x2 : ℕ) (h1 : x1 = m + 1) (h2 : x2 = m + 2) :
    ((m : ℤ) + 2) ^ 2 * franel x2 =
      (7 * (m : ℤ) ^ 2 + 21 * m + 16) * franel x1 + 8 * ((m : ℤ) + 1) ^ 2 * franel m := by
  subst h1 h2
  have r := frec m
  exact_mod_cast r

end P110707

theorem OMA.solution : type_of% @OMA.S_oeis_a110707.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have r0 := P110707.fz m (m + 1) (m + 2) rfl rfl
  have r1 := P110707.fz (m + 1) (m + 2) (m + 3) rfl rfl
  have r2 := P110707.fz (m + 2) (m + 3) (m + 4) rfl rfl
  have e0 : a (m + 4) = 2 * (franel (m + 3) : ℤ) + 2 * (franel (m + 4) : ℤ) := rfl
  have e1 : a (m + 4 - 1) = 2 * (franel (m + 2) : ℤ) + 2 * (franel (m + 3) : ℤ) := by
    rw [show m + 4 - 1 = m + 3 by omega]; rfl
  have e2 : a (m + 4 - 2) = 2 * (franel (m + 1) : ℤ) + 2 * (franel (m + 2) : ℤ) := by
    rw [show m + 4 - 2 = m + 2 by omega]; rfl
  have e3 : a (m + 4 - 3) = 2 * (franel m : ℤ) + 2 * (franel (m + 1) : ℤ) := by
    rw [show m + 4 - 3 = m + 1 by omega]; rfl
  rw [e0, e1, e2, e3]
  push_cast at r0 r1 r2 ⊢
  linear_combination 2 * r0 + 4 * r1 + 2 * r2
