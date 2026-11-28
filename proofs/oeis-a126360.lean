import OMAStatements.S_oeis_a126360

namespace OMA.S_oeis_a126360

open Finset Matrix PowerSeries

lemma cube_ones : adjacency *ᵥ (adjacency *ᵥ (adjacency *ᵥ ones)) =
    (4 : ℤ) • (adjacency *ᵥ (adjacency *ᵥ ones)) - (3 : ℤ) • (adjacency *ᵥ ones) - ones := by
  decide

lemma pow_step (n : ℕ) : adjacency ^ (n + 3) *ᵥ ones =
    (4 : ℤ) • (adjacency ^ (n + 2) *ᵥ ones) - (3 : ℤ) • (adjacency ^ (n + 1) *ᵥ ones) -
      adjacency ^ n *ᵥ ones := by
  simp only [pow_succ, ← Matrix.mulVec_mulVec]
  rw [cube_ones, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_smul]

lemma a_rec (m : ℕ) : a (m + 4) = 4 * a (m + 3) - 3 * a (m + 2) - a (m + 1) := by
  simp only [a]
  rw [pow_step m]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma a0 : a 0 = 1 := rfl
lemma a1 : a 1 = 6 := by decide
lemma a2 : a 2 = 16 := by decide
lemma a3 : a 3 = 44 := by decide

theorem solution_main :
    (∀ n : ℕ, 3 < n → a n = 4 * a (n - 1) - 3 * a (n - 2) - a (n - 3)) ∧
      denominator * generating = numerator := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    exact a_rec m
  · ext k
    have hd : denominator * generating =
        X ^ 3 * generating + C (3 : ℤ) * (X ^ 2 * generating) - C (4 : ℤ) * (X ^ 1 * generating) +
          generating := by
      simp only [denominator]; ring
    rw [hd]
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', generating, coeff_mk,
      numerator, coeff_X_pow, coeff_C, coeff_X, coeff_one, map_neg]
    match k with
    | 0 => simp [a0]
    | 1 => simp [a0, a1]
    | 2 => simp [a0, a1, a2]
    | 3 => simp [a0, a1, a2, a3]
    | m + 4 =>
      simp only [show m + 4 - 3 = m + 1 by omega, show m + 4 - 2 = m + 2 by omega,
        show m + 4 - 1 = m + 3 by omega]
      rw [a_rec m]
      simp
      ring

end OMA.S_oeis_a126360

theorem OMA.solution : type_of% @OMA.S_oeis_a126360.main := OMA.S_oeis_a126360.solution_main
