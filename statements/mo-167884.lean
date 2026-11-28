import Mathlib

/-!
# Inverse infinity norm of a weakly diagonally dominant Z-matrix

Source: Joshuald1986, https://mathoverflow.net/questions/167884 (CC BY-SA).
Credit: @connoranderson. The example makes precise fedja's perturbation
observation in the source comments. The second clause gives an entry-dependent
bound using a finite power of the nonnegative matrix I-A.
-/

namespace OMA.S_mo_167884
open Matrix Finset
open scoped Matrix.Norms.Operator

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def off {n : ℕ} (A : Mat n) (i : Fin n) : ℝ :=
  ∑ j, if i=j then 0 else |A i j|
def Admissible {n : ℕ} (A : Mat n) (b : Fin n → ℝ) : Prop :=
  (∀ i, A i i = 1) ∧ (∀ i j, i≠j → -1 ≤ A i j ∧ A i j ≤ 0) ∧
  (∀ i, off A i=0 ∨ off A i=1) ∧ (∃ i, off A i=1) ∧ (∃ i, off A i=0) ∧
  (∀ i, b i=0 ∨ b i=1) ∧ (∀ i, b i=1 → off A i=0) ∧ IsUnit A.det

theorem main :
    (∀ M : ℝ, ∃ (A : Mat 3) (b : Fin 3 → ℝ), Admissible A b ∧
      (∃ i, b i=1) ∧ ‖A‖=2 ∧ M < ‖A⁻¹‖) ∧
    (∀ n : ℕ, ∀ (A : Mat n) (b : Fin n → ℝ), Admissible A b →
      (∃ k : ℕ, ‖((1-A)^k)‖ < 1) ∧ ∀ k : ℕ,
      ‖((1-A)^k)‖ < 1 → ‖A⁻¹‖ ≤ k/(1-‖((1-A)^k)‖)) := by
  sorry
end OMA.S_mo_167884
