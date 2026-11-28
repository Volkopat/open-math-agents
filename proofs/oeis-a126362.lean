import OMAStatements.S_oeis_a126362

namespace OMA.S_oeis_a126362

open Finset Matrix PowerSeries

lemma four_ones : adjacency *ᵥ (adjacency *ᵥ (adjacency *ᵥ (adjacency *ᵥ ones))) =
    (5 : ℤ) • (adjacency *ᵥ (adjacency *ᵥ (adjacency *ᵥ ones))) -
      (6 : ℤ) • (adjacency *ᵥ (adjacency *ᵥ ones)) - adjacency *ᵥ ones + (2 : ℤ) • ones := by
  decide

lemma pow_step (n : ℕ) : adjacency ^ (n + 4) *ᵥ ones =
    (5 : ℤ) • (adjacency ^ (n + 3) *ᵥ ones) - (6 : ℤ) • (adjacency ^ (n + 2) *ᵥ ones) -
      adjacency ^ (n + 1) *ᵥ ones + (2 : ℤ) • (adjacency ^ n *ᵥ ones) := by
  have e4 : adjacency ^ (n + 4) *ᵥ ones =
      adjacency ^ n *ᵥ (adjacency *ᵥ (adjacency *ᵥ (adjacency *ᵥ (adjacency *ᵥ ones)))) := by
    simp only [Matrix.mulVec_mulVec]
    congr 1
    simp [pow_succ, mul_assoc]
  have e3 : adjacency ^ (n + 3) *ᵥ ones =
      adjacency ^ n *ᵥ (adjacency *ᵥ (adjacency *ᵥ (adjacency *ᵥ ones))) := by
    simp only [Matrix.mulVec_mulVec]
    congr 1
    simp [pow_succ, mul_assoc]
  have e2 : adjacency ^ (n + 2) *ᵥ ones = adjacency ^ n *ᵥ (adjacency *ᵥ (adjacency *ᵥ ones)) := by
    simp only [Matrix.mulVec_mulVec]
    congr 1
    simp [pow_succ, mul_assoc]
  have e1 : adjacency ^ (n + 1) *ᵥ ones = adjacency ^ n *ᵥ (adjacency *ᵥ ones) := by
    simp only [Matrix.mulVec_mulVec, pow_succ]
  rw [e4, e3, e2, e1, four_ones, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]

lemma a_rec (m : ℕ) :
    a (m + 5) = 5 * a (m + 4) - 6 * a (m + 3) - a (m + 2) + 2 * a (m + 1) := by
  simp only [a]
  rw [pow_step m]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma a0 : a 0 = 1 := rfl
lemma a1 : a 1 = 8 := by decide
lemma a2 : a 2 = 22 := by decide
lemma a3 : a 3 = 62 := by decide
lemma a4 : a 4 = 176 := by decide

theorem solution_main :
    (∀ n : ℕ, 4 < n → a n = 5 * a (n - 1) - 6 * a (n - 2) - a (n - 3) + 2 * a (n - 4)) ∧
      denominator * generating = numerator := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    exact a_rec m
  · ext k
    have hd : denominator * generating =
        -(C (2 : ℤ) * (X ^ 4 * generating)) + X ^ 3 * generating + C (6 : ℤ) * (X ^ 2 * generating)
          - C (5 : ℤ) * (X ^ 1 * generating) + generating := by
      simp only [denominator]; ring
    rw [hd]
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', generating, coeff_mk,
      numerator, coeff_X_pow, coeff_X, coeff_one]
    match k with
    | 0 => simp [a0]
    | 1 => simp [a0, a1]
    | 2 => simp [a0, a1, a2]
    | 3 => simp [a0, a1, a2, a3]
    | 4 => simp [a0, a1, a2, a3, a4]
    | m + 5 =>
      simp only [show m + 5 - 4 = m + 1 by omega, show m + 5 - 3 = m + 2 by omega,
        show m + 5 - 2 = m + 3 by omega, show m + 5 - 1 = m + 4 by omega]
      rw [a_rec m]
      simp
      ring

end OMA.S_oeis_a126362

theorem OMA.solution : type_of% @OMA.S_oeis_a126362.main := OMA.S_oeis_a126362.solution_main
