import OMAStatements.S_oeis_a192755
import Mathlib

-- Original proof by @justusklocke-cloud. Statement by @JeremyDevs.

namespace A192755
open Polynomial OMA.S_oeis_a192755

/-- The pair (constant coefficient, coefficient of X) of the reduction of p n. -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((uv n).2 + (5 * ((n : ℤ) + 1) + 1), (uv n).1 + (uv n).2)

lemma p_eq (n : ℕ) : ∃ q : ℤ[X], p n
    = (X ^ 2 - X - 1) * q + (C (uv n).1 + C (uv n).2 * X) := by
  induction n with
  | zero => exact ⟨0, by simp [p, uv]⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨X * q + C (uv n).2, ?_⟩
    rw [p, hq, uv]
    simp only [map_add]
    ring

lemma monicQ : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

lemma a_eq (n : ℕ) : a n = (uv n).2 := by
  obtain ⟨q, hq⟩ := p_eq n
  have hd : (C (uv n).1 + C (uv n).2 * X : ℤ[X]).degree <
      (X ^ 2 - X - 1 : ℤ[X]).degree := by
    rw [show (X ^ 2 - X - 1 : ℤ[X]).degree = 2 by compute_degree!]
    compute_degree!
  rw [a, hq, add_modByMonic, self_mul_modByMonic monicQ, zero_add,
    (modByMonic_eq_self_iff monicQ).mpr hd]
  rw [coeff_add, coeff_C_mul, coeff_X_one, coeff_C]
  simp

end A192755

open PowerSeries A192755 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192755.main := by
  rw [show OMA.S_oeis_a192755.a = fun n => (uv n).2 from funext a_eq]
  have hD : (((X : PowerSeries ℤ) ^ 2 + X - 1) * (X - 1) ^ 2)
      = C (-1) * X ^ 0 + C 3 * X ^ 1 + C (-2) * X ^ 2 + C (-1) * X ^ 3 + C 1 * X ^ 4 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hN : -(X : PowerSeries ℤ) * (1 + 4 * X) = C (-1) * X ^ 1 + C (-4) * X ^ 2 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  rw [hD, hN]
  ext n
  simp only [mul_add, map_add, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C, coeff_mk, coeff_C]
  rcases n with _ | _ | _ | _ | n <;> simp [uv]
  ring
