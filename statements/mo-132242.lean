import Mathlib

/-!
# Kernel of a bivariate Vandermonde matrix

Source: trion, https://mathoverflow.net/questions/132242 (CC BY-SA 3.0).
Credit: @connoranderson.

The rows correspond to the monomials of separate degrees less than m.
A signed maximal-minor vector spans the nullspace when nonzero. A row basis
gives a projector formula at every rank. Distinct points alone can have
nullity greater than one.
-/

namespace OMA.S_mo_132242

open scoped Matrix

noncomputable def vand (m : ℕ) (x y : Fin (m*m+1) → ℝ) :
    Matrix (Fin m × Fin m) (Fin (m*m+1)) ℝ :=
  fun ab j => x j ^ ab.1.val * y j ^ ab.2.val

noncomputable def cof {d : ℕ} (A : Matrix (Fin d) (Fin (d+1)) ℝ) (j : Fin (d+1)) : ℝ :=
  (-1 : ℝ) ^ j.val * (A.submatrix id j.succAbove).det

theorem main : (∀ (m : ℕ) (x y : Fin (m*m+1) → ℝ),
    Function.Injective (fun j => (x j,y j)) →
    let V := vand m x y
    let A := V.submatrix finProdFinEquiv.symm id
    (A *ᵥ cof A = 0 ∧ (cof A ≠ 0 → ∀ v, A *ᵥ v = 0 ↔ ∃ c : ℝ, v = c • cof A)) ∧
    ∃ s : Finset (Fin m × Fin m),
      let B := V.submatrix (fun i : s => (i : Fin m × Fin m)) id
      ∀ v, V *ᵥ v = 0 ↔ ∃ w, v = (1 - B.transpose * (B * B.transpose)⁻¹ * B) *ᵥ w) ∧
    ∀ m : ℕ, 2 ≤ m → ∃ x y : Fin (m*m+1) → ℝ,
      Function.Injective (fun j => (x j,y j)) ∧
      1 < Module.finrank ℝ (LinearMap.ker (vand m x y).mulVecLin) := by
  sorry

end OMA.S_mo_132242
