import Mathlib

/-!
# A pseudodeterminant update without a range condition

Source: Gattocrucco, https://mathoverflow.net/questions/440872 (CC BY-SA 4.0).
Credit: @connoranderson.

For arbitrary update columns U, let P project orthogonally onto the kernel of
the original positive semidefinite matrix A, and let D be its Moore–Penrose
inverse. For positive definite W put G = UᵀPU and H = W⁻¹ + UᵀDU. The update
multiplier for the pseudodeterminant is det(W) det(H) pdet(H⁻¹G). All three
matrices in this multiplier have the size of W. When the columns of U lie in
the image of A, G vanishes and its pseudodeterminant factor is one.

The pencil identity also covers singular positive semidefinite W. Its trailing
coefficient is the coefficient of its lowest nonzero power. The proof
regularizes A on its kernel and applies a block determinant identity.
-/
namespace OMA.S_mo_440872
open Matrix Polynomial Finset
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Rect (n k : ℕ) := Matrix (Fin n) (Fin k) ℝ

noncomputable def pdet {n : ℕ} (A : Mat n) : ℝ := (-A).charpoly.trailingCoeff
noncomputable def spectral {n : ℕ} {A : Mat n} (h : A.IsHermitian) (f : ℝ → ℝ) : Mat n :=
  Unitary.conjStarAlgAut ℝ _ h.eigenvectorUnitary (diagonal fun i => f (h.eigenvalues i))

noncomputable def pinv {n : ℕ} {A : Mat n} (h : A.IsHermitian) : Mat n :=
  spectral h (fun x => x⁻¹)
noncomputable def kernelProj {n : ℕ} {A : Mat n} (h : A.IsHermitian) : Mat n :=
  spectral h (fun x => if x=0 then 1 else 0)

noncomputable def pencil {n : ℕ} (G H : Mat n) : Matrix (Fin n) (Fin n) ℝ[X] :=
  G.map C + (X:ℝ[X]) • H.map C

theorem main :
    (∀ {n : ℕ} (A : Mat n) (h : A.IsHermitian), pdet A =
       ∏ i, if h.eigenvalues i=0 then 1 else h.eigenvalues i) ∧
    (∀ {n k : ℕ} (A : Mat n) (U : Rect n k) (W : Mat k) (hA : A.PosSemidef),
      W.PosSemidef → pdet (A+U*W*Uᵀ)=pdet A *
        (pencil (W*Uᵀ*kernelProj hA.1*U) (1+W*Uᵀ*pinv hA.1*U)).det.trailingCoeff) ∧
    (∀ {n k : ℕ} (A : Mat n) (U : Rect n k) (W : Mat k) (hA : A.PosSemidef),
      W.PosDef →
      let G := Uᵀ * kernelProj hA.1 * U
      let H := W⁻¹ + Uᵀ * pinv hA.1 * U
      pdet (A+U*W*Uᵀ) = pdet A * W.det * (pencil G H).det.trailingCoeff ∧
      pdet (A+U*W*Uᵀ) = pdet A * W.det * H.det * pdet (H⁻¹*G)) ∧
    (∀ {n k : ℕ} (A : Mat n) (U : Rect n k) (W : Mat k) (hA : A.PosSemidef),
      W.PosDef → kernelProj hA.1*U=0 →
      pdet (A+U*W*Uᵀ) = pdet A*W.det*(W⁻¹+Uᵀ*pinv hA.1*U).det) ∧
    (∀ {n : ℕ} (A : Mat n) (U : Rect n 1) (W : Mat 1) (hA : A.PosSemidef),
      W.PosSemidef →
      let g := (W*Uᵀ*kernelProj hA.1*U) 0 0
      let h := (1+W*Uᵀ*pinv hA.1*U : Mat 1) 0 0
      pdet (A+U*W*Uᵀ) = pdet A*(if g=0 then h else g)) := by
  sorry

end OMA.S_mo_440872
