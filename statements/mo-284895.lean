import Mathlib

/-!
# A fixed diagonal direction separating singular values

Source: Dominique Unruh, https://mathoverflow.net/questions/284895 (CC BY-SA 3.0).
Credit: @connoranderson.

The question asks whether an arbitrarily small complex symmetric perturbation
can make all singular values of a complex square matrix distinct. The same
real diagonal direction D = diag(1,2,...,n) works for every input matrix.
Only finitely many real parameters give a repeated singular value.
-/
namespace OMA.S_mo_284895
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
noncomputable def direction (n : ℕ) : Mat n := diagonal (fun i => (i.val+1:ℂ))
noncomputable def singular {n : ℕ} (M : Mat n) (i : Fin n) : ℝ :=
  Real.sqrt ((posSemidef_conjTranspose_mul_self M).1.eigenvalues i)
def simple {n : ℕ} (M : Mat n) : Prop := Function.Injective (singular M)

theorem main : ∀ (n : ℕ) (A : Mat n),
    {t : ℝ | ¬ simple (A+(t:ℂ) • direction n)}.Finite ∧
    ∀ ε : ℝ, 0 < ε → ∃ (t : ℝ) (S : Mat n), 0 < t ∧ S=(t:ℂ) • direction n ∧ Sᵀ=S ∧
      ‖S‖ < ε ∧ simple (A+S) := by
  sorry
end OMA.S_mo_284895
