import Mathlib

/-!
# Near-isometries of the Hamming cube

Source https://mathoverflow.net/questions/172723/are-there-any-nontrivial-near-isometries-of-the-n-dimensional-cube

A real orthogonal matrix with polynomially large average absolute
coordinate product on the cube is conjectured to have a permutation
diagonal with polynomially large absolute product.
-/

namespace OMA.S_mo_172723

open scoped BigOperators

noncomputable def cubeScore {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∑ x : Fin n → Bool, |∏ i : Fin n,
    (O.mulVec (fun j => if x j then 1 else -1)) i|) / (2 : ℝ) ^ n

theorem main :
    ∀ C : ℝ, 0 < C → ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ O : Matrix (Fin n) (Fin n) ℝ,
        O.transpose * O = 1 →
        Real.rpow (n : ℝ) (-C) ≤ cubeScore O →
        ∃ σ : Equiv.Perm (Fin n), Real.rpow (n : ℝ) (-D) ≤
          |∏ i : Fin n, O i (σ i)| := by
  sorry

end OMA.S_mo_172723
