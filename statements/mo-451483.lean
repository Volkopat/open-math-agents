import Mathlib

/-!
# Sharp Frobenius bounds for the exponential of anti-Hermitian matrices

Source: Haimeng Zhao, https://mathoverflow.net/questions/451483 (CC BY-SA 4.0).
Credit: @connoranderson.
The endpoint obstruction was noted in the original discussion by Terry Tao and
fedja. Write the anti-Hermitian matrices as iA and iB with A and B Hermitian.
Bounding their operator norms by r is equivalent to bounding the absolute
values of the eigenvalues of A and B by r. We use squared Frobenius norms.
For 0 < r ≤ π the sharp lower factor in the unsquared norm is sin(r)/r.
It vanishes at the radius π asked about in the question.
-/

namespace OMA.S_mo_451483
open Matrix Finset
open scoped Matrix.Norms.L2Operator

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
noncomputable def froSq {n : ℕ} (A : Mat n) : ℝ := ∑ i,∑ j, ‖A i j‖^2
noncomputable def phase {n : ℕ} (A : Mat n) : Mat n := NormedSpace.exp (Complex.I • A)
noncomputable def scalar (x : ℝ) : Mat 1 := diagonal (fun _ => (x:ℂ))

theorem main :
    (∀ (r : ℝ), 0<r → r≤Real.pi → ∀ (n : ℕ) (A B : Mat n)
      (hA : A.IsHermitian) (hB : B.IsHermitian),
      (∀ i, |hA.eigenvalues i|≤r) → (∀ j, |hB.eigenvalues j|≤r) →
      (Real.sin r/r)^2 * froSq (A-B) ≤ froSq (phase A-phase B) ∧
      froSq (phase A-phase B) ≤ froSq (A-B)) ∧
    (∀ r : ℝ, 0<r → r≤Real.pi →
      0 < froSq (scalar r - scalar (-r)) ∧
      froSq (phase (scalar r) - phase (scalar (-r))) =
        (Real.sin r/r)^2 * froSq (scalar r - scalar (-r))) := by
  sorry
end OMA.S_mo_451483
