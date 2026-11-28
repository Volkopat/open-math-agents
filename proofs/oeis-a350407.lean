import OMAStatements.S_oeis_a350407
import Mathlib

namespace OMA.A350407Proof

open OMA.S_oeis_a350407 PowerSeries

lemma hg : g * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) = 1 := by
  unfold g
  apply PowerSeries.invOfUnit_mul
  simp

lemma hdvd : (X : PowerSeries ℤ) ^ 6 ∣ g - (1 - X + X ^ 5) := by
  have h1 : (1 - X + X ^ 5 : PowerSeries ℤ) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) = 1 + X ^ 6 * (1 + X + X ^ 2 + X ^ 3) := by ring
  have h2 : g - (1 - X + X ^ 5) = - (X ^ 6 * (1 + X + X ^ 2 + X ^ 3) * g) := by
    have : (g - (1 - X + X ^ 5)) = (g - (1 - X + X ^ 5)) * ((1 + X + X ^ 2 + X ^ 3 + X ^ 4) * g) := by
      rw [mul_comm (1 + X + X ^ 2 + X ^ 3 + X ^ 4) g, hg, mul_one]
    rw [this]
    have e : (g - (1 - X + X ^ 5)) * ((1 + X + X ^ 2 + X ^ 3 + X ^ 4) * g) =
        g * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * g - (1 - X + X ^ 5) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * g := by ring
    rw [e, hg, h1]; ring
  rw [h2]
  exact (Dvd.intro ((1 + X + X ^ 2 + X ^ 3) * g) (by ring) : (X : PowerSeries ℤ) ^ 6 ∣ X ^ 6 * (1 + X + X ^ 2 + X ^ 3) * g).neg_right

lemma coeff_low (m : ℕ) (hm : m < 6) : coeff m (g ^ 5) = coeff m ((1 - X + X ^ 5 : PowerSeries ℤ) ^ 5) := by
  have h : (X : PowerSeries ℤ) ^ 6 ∣ g ^ 5 - (1 - X + X ^ 5) ^ 5 :=
    (hdvd).trans (sub_dvd_pow_sub_pow _ _ 5)
  have := (PowerSeries.X_pow_dvd_iff.1 h) m hm
  rw [map_sub] at this
  linarith

lemma hh5 : (1 - X + X ^ 5 : PowerSeries ℤ) ^ 5 = C (1:ℤ) * X ^ 0 + C (-5:ℤ) * X ^ 1 + C (10:ℤ) * X ^ 2 + C (-10:ℤ) * X ^ 3 + C (5:ℤ) * X ^ 4 + C (4:ℤ) * X ^ 5 + C (-20:ℤ) * X ^ 6 + C (30:ℤ) * X ^ 7 + C (-20:ℤ) * X ^ 8 + C (5:ℤ) * X ^ 9 + C (10:ℤ) * X ^ 10 + C (-30:ℤ) * X ^ 11 + C (30:ℤ) * X ^ 12 + C (-10:ℤ) * X ^ 13 + C (10:ℤ) * X ^ 15 + C (-20:ℤ) * X ^ 16 + C (10:ℤ) * X ^ 17 + C (5:ℤ) * X ^ 20 + C (-5:ℤ) * X ^ 21 + C (1:ℤ) * X ^ 25 := by
  simp only [map_ofNat, map_neg, map_one]
  ring

lemma a5 : a 5 = 4 := by
  unfold a
  rw [coeff_low 5 (by norm_num), hh5]
  simp only [map_add, coeff_C_mul, coeff_X_pow]
  norm_num

lemma a1 : a 1 = -1 := by
  unfold a
  have := (PowerSeries.X_pow_dvd_iff.1 hdvd) 1 (by norm_num)
  rw [map_sub] at this
  rw [pow_one]
  simp at this
  linarith

end OMA.A350407Proof

open OMA.A350407Proof OMA.S_oeis_a350407 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a350407.main) := by
  intro h
  have := h 1 1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [a5, a1, Int.ModEq] at this

#print axioms OMA.disproof
