import Mathlib

/-!
# Generalized Cauchy matrices from elementary symmetric polynomials

Source: Suvrit Sra, https://mathoverflow.net/questions/114101 (CC BY-SA 3.0).
Credit: @connoranderson

For the k-th elementary symmetric polynomial we sum over k-element subsets.
The question asks whether every generalized Cauchy matrix is positive
semidefinite. Its negation asks for a family of vectors in the open cube
and an allowed k for which the resulting real matrix is not positive semidefinite.
-/

namespace OMA.S_mo_114101

noncomputable def elementary {n : ℕ} (k : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ j ∈ T, v j

noncomputable def cauchy {m n : ℕ} (k : ℕ) (x : Fin m → Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (elementary k (fun l => 1-x i l*x j l))⁻¹

theorem main : ∃ (m n k : ℕ) (x : Fin m → Fin n → ℝ),
    0 < m ∧ 1 ≤ k ∧ k ≤ n ∧ (∀ i j, |x i j| < 1) ∧ ¬ (cauchy k x).PosSemidef := by
  sorry

end OMA.S_mo_114101
