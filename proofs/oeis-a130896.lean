import OMAStatements.S_oeis_a130896
import Mathlib

-- Problem: A130896, the {F, V, E, dimension} quadruples for pyramid-like D_n type polyhedra.
-- Upstream: formal-conjectures statements/oeis-a130896.lean (declaration OMA.S_oeis_a130896.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: the denominator is (1 - x^4)^3, and within each residue class modulo 4 the terms are
-- polynomials of degree at most 2 in the block index, so their third differences vanish; the
-- first twelve coefficients are checked directly.

namespace OMA.P_oeis_a130896

open OMA.S_oeis_a130896 PowerSeries

theorem a_block (q r : ℕ) (hr : r < 4) : a (4 * q + r + 1) = quad (q + 1) r := by
  unfold a
  rw [if_neg (by omega), show 4 * q + r + 1 - 1 = 4 * q + r by omega,
    show (4 * q + r) / 4 = q by omega, show (4 * q + r) % 4 = r by omega]

theorem half (m : ℕ) : (((2 * m + 1) * ((2 * m + 1) - 1) / 2 : ℕ) : ℤ) = (2 * m + 1) * m := by
  rw [show (2 * m + 1) - 1 = 2 * m by omega, show (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  ring

theorem rec12 (k : ℕ) :
    (a (k + 13) : ℤ) = 3 * a (k + 9) - 3 * a (k + 5) + a (k + 1) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ k = 4 * q + r :=
    ⟨k / 4, k % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 4).symm⟩
  rw [show 4 * q + r + 13 = 4 * (q + 3) + r + 1 by ring, show 4 * q + r + 9 = 4 * (q + 2) + r + 1 by ring,
    show 4 * q + r + 5 = 4 * (q + 1) + r + 1 by ring, a_block _ _ hr, a_block _ _ hr, a_block _ _ hr,
    a_block _ _ hr]
  unfold quad
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl
  · simp only [↓reduceIte]; push_cast; ring
  · simp only [show (1 : ℕ) ≠ 0 by norm_num, ↓reduceIte]; push_cast; ring
  · simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
    push_cast; ring
  · simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
      show (3 : ℕ) ≠ 2 by norm_num, ↓reduceIte]
    rw [half, half, half, half]
    push_cast; ring

theorem part1 :
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 3) =
      X * (3 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 - 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 +
        X ^ 8 + X ^ 9) := by
  have hden : ((1 - X) ^ 3 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 3 : PowerSeries ℤ) =
      1 - C (3 : ℤ) * X ^ 4 + C (3 : ℤ) * X ^ 8 - X ^ 12 := by
    simp only [map_ofNat]
    ring
  have hnum : (X * (3 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 - 4 * X ^ 5 - 4 * X ^ 6 +
      X ^ 7 + X ^ 8 + X ^ 9) : PowerSeries ℤ) =
      C (3 : ℤ) * X ^ 1 + C (3 : ℤ) * X ^ 2 + C (4 : ℤ) * X ^ 3 + C (3 : ℤ) * X ^ 4 +
      C (-4 : ℤ) * X ^ 5 + C (-4 : ℤ) * X ^ 6 + C (-4 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 +
      C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 10 := by
    simp only [map_ofNat, map_one, map_neg]
    ring
  rw [hden, hnum]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk _) (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;> norm_num [a, quad]
  · simp only [show 4 ≤ n by omega, show 8 ≤ n by omega, show 12 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega,
      show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega, show n - 9 ≠ 0 by omega,
      show n - 10 ≠ 0 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 5 ≤ n by omega,
      show 6 ≤ n by omega, show 7 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega,
      ↓reduceIte]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
    rw [show k + 13 - 4 = k + 9 by omega, show k + 13 - 8 = k + 5 by omega,
      show k + 13 - 12 = k + 1 by omega, rec12]
    ring

theorem part2 : ∀ n : ℕ, 12 < n → (a n : ℤ) = 3 * a (n - 4) - 3 * a (n - 8) + a (n - 12) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
  rw [show k + 13 - 4 = k + 9 by omega, show k + 13 - 8 = k + 5 by omega,
    show k + 13 - 12 = k + 1 by omega, rec12]

end OMA.P_oeis_a130896

theorem OMA.solution : type_of% @OMA.S_oeis_a130896.main :=
  ⟨OMA.P_oeis_a130896.part1, OMA.P_oeis_a130896.part2⟩
