import OMAStatements.S_oeis_a138365
import Mathlib

namespace A138365

open PowerSeries

lemma coeff_den (f : ℕ → ℤ) (n : ℕ) :
    coeff n (mk f * (C (1 : ℤ) * (X : PowerSeries ℤ) ^ 3 + C (-10 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (-10 : ℤ) * (X : PowerSeries ℤ) ^ 1 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0)) =
    (1 : ℤ) * (if 3 ≤ n then f (n - 3) else 0) + (-10 : ℤ) * (if 2 ≤ n then f (n - 2) else 0) + (-10 : ℤ) * (if 1 ≤ n then f (n - 1) else 0) + (1 : ℤ) * (if 0 ≤ n then f (n - 0) else 0) := by
  have e : mk f * (C (1 : ℤ) * (X : PowerSeries ℤ) ^ 3 + C (-10 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (-10 : ℤ) * (X : PowerSeries ℤ) ^ 1 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0) =
      C (1 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 3) + C (-10 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 2) + C (-10 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 1) + C (1 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 0) := by
    ring
  rw [e]
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

lemma b_rec (k : ℕ) : OMA.S_oeis_a138365.b (k + 2) =
    3 * OMA.S_oeis_a138365.b (k + 1) + OMA.S_oeis_a138365.b k := by
  rw [OMA.S_oeis_a138365.b]

lemma f_eq (k : ℕ) : (if k = 0 then (0 : ℤ) else OMA.S_oeis_a138365.a k) = OMA.S_oeis_a138365.a k := by
  split_ifs with h
  · rw [h]
    simp [OMA.S_oeis_a138365.a, OMA.S_oeis_a138365.b]
  · rfl

lemma rec3 (k : ℕ) : OMA.S_oeis_a138365.a (k + 3) - 10 * OMA.S_oeis_a138365.a (k + 2)
    - 10 * OMA.S_oeis_a138365.a (k + 1) + OMA.S_oeis_a138365.a k = 0 := by
  unfold OMA.S_oeis_a138365.a
  have h2 := b_rec k
  have h3 : OMA.S_oeis_a138365.b (k + 3) =
      3 * OMA.S_oeis_a138365.b (k + 2) + OMA.S_oeis_a138365.b (k + 1) := b_rec (k + 1)
  have h4 : OMA.S_oeis_a138365.b (k + 4) =
      3 * OMA.S_oeis_a138365.b (k + 3) + OMA.S_oeis_a138365.b (k + 2) := b_rec (k + 2)
  have h5 : OMA.S_oeis_a138365.b (k + 5) =
      3 * OMA.S_oeis_a138365.b (k + 4) + OMA.S_oeis_a138365.b (k + 3) := b_rec (k + 3)
  rw [show k + 3 + 2 = k + 5 by ring, show k + 2 + 2 = k + 4 by ring,
    show k + 1 + 2 = k + 3 by ring, h5, h4, h3, h2]
  ring

end A138365

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a138365.main := by
  have hden : ((X : PowerSeries ℤ) + 1) * ((X : PowerSeries ℤ) ^ 2 - 11 * (X : PowerSeries ℤ) + 1) =
      C (1 : ℤ) * (X : PowerSeries ℤ) ^ 3 + C (-10 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (-10 : ℤ) * (X : PowerSeries ℤ) ^ 1 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0 := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  have hnum : -(X : PowerSeries ℤ) * ((X : PowerSeries ℤ) - 10) =
      C (-1 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (10 : ℤ) * (X : PowerSeries ℤ) ^ 1 := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  ext n
  rw [hden, hnum, A138365.coeff_den]
  simp only [map_add, coeff_C_mul, coeff_X_pow, A138365.f_eq]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | rfl | h3
  · simp [OMA.S_oeis_a138365.a, OMA.S_oeis_a138365.b]
  · simp [OMA.S_oeis_a138365.a, OMA.S_oeis_a138365.b]
  · simp [OMA.S_oeis_a138365.a, OMA.S_oeis_a138365.b]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have h := A138365.rec3 k
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega),
      show k + 3 - 3 = k by omega, show k + 3 - 2 = k + 1 by omega,
      show k + 3 - 1 = k + 2 by omega, show k + 3 - 0 = k + 3 by omega]
    linarith
