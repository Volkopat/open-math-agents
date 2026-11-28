import OMAStatements.S_oeis_a055040
import Mathlib

/-!
Refutation at the coefficient of x^1. On the left it is a(1) - 0 = a(1), the least number of
the form 3^(2i+1)(3j+2); on the right it is 2. But 2 is not of that form (3 does not divide 2),
while the least element of a nonempty set of naturals belongs to it, so a(1) is not 2.
-/

namespace R055040
open OMA.S_oeis_a055040 PowerSeries

theorem not_two : ¬ IsTerm 2 := by
  rintro ⟨i, j, h⟩
  have h3 : 3 ∣ 3 ^ (2 * i + 1) * (3 * j + 2) :=
    Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
  rw [← h] at h3
  omega

theorem a1_ne : a 1 ≠ 2 := by
  intro h
  have h' : Nat.nth IsTerm 0 = 2 := h
  have hne : (Set.ofPred IsTerm).Nonempty := ⟨6, show IsTerm 6 from ⟨0, 0, by norm_num⟩⟩
  have hmem := Nat.sInf_mem hne
  rw [Nat.nth_zero] at h'
  rw [h'] at hmem
  exact not_two hmem

theorem eL (p : ℤ⟦X⟧) : coeff 1 (p * (X ^ 11 - X ^ 10 - X + 1)) = coeff 1 p - coeff 0 p := by
  rw [show p * (X ^ 11 - X ^ 10 - X + 1) = p * X ^ 11 - p * X ^ 10 - p * X ^ 1 + p by ring]
  simp only [map_add, map_sub, coeff_mul_X_pow']
  rw [if_neg (by norm_num : ¬ (11 ≤ 1)), if_neg (by norm_num : ¬ (10 ≤ 1)),
    if_pos (le_refl 1), Nat.sub_self]
  ring

theorem eR : coeff 1 (X * (X + 2) * (X ^ 2 + X + 1) * (X ^ 7 + X ^ 3 + 1) : ℤ⟦X⟧) = 2 := by
  have e : (X * (X + 2) * (X ^ 2 + X + 1) * (X ^ 7 + X ^ 3 + 1) : ℤ⟦X⟧) =
      X * ((X + 2) * (X ^ 2 + X + 1) * (X ^ 7 + X ^ 3 + 1)) := by ring
  have e2 : coeff 1 (X * ((X + 2) * (X ^ 2 + X + 1) * (X ^ 7 + X ^ 3 + 1)) : ℤ⟦X⟧) =
      coeff 0 ((X + 2) * (X ^ 2 + X + 1) * (X ^ 7 + X ^ 3 + 1) : ℤ⟦X⟧) :=
    coeff_succ_X_mul 0 _
  rw [e, e2]
  simp
  rw [show (2 : ℤ⟦X⟧) = 1 + 1 by norm_num, map_add, map_one] <;> norm_num

end R055040

open OMA.S_oeis_a055040 R055040 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a055040.main) := by
  intro h
  have h1 : coeff 1 (A * ((X : ℤ⟦X⟧) ^ 11 - X ^ 10 - X + 1)) =
      coeff 1 (X * (X + 2) * (X ^ 2 + X + 1) * (X ^ 7 + X ^ 3 + 1) : ℤ⟦X⟧) := by
    rw [h]
  rw [eL, eR] at h1
  simp only [A, coeff_mk] at h1
  simp at h1
  exact a1_ne (by exact_mod_cast h1)
