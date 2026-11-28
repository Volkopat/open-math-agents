import Mathlib

/-!
# Best scalar operator-norm approximation and the loss from Frobenius projection

Source: Conner DiPaolo, https://mathoverflow.net/questions/271853 (CC BY-SA).
Credit: @connoranderson. The block semidefinite formulation is due to Suvrit in
the source discussion; fedja suggested looking at diagonal matrices to assess
the loss. The worst-case approximation factor is exactly (1+√n)/2 for n×n
complex matrices. For rectangular matrices n is replaced by the smaller
dimension. The last clause gives the optimizing scalar for the author's
application with X=I and Y positive definite.
-/

namespace OMA.S_mo_271853
open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ
noncomputable def coef {m n : ℕ} (X Y : Mat m n) : ℂ :=
  (∑ i,∑ j, star (Y i j)*X i j) / ((∑ i,∑ j, ‖Y i j‖^2 : ℝ) : ℂ)

theorem main :
    (∀ m n, ∀ (X Y : Mat m n) (z : ℂ) (t : ℝ), 0≤t →
      (‖X-z•Y‖ ≤ t ↔ (fromBlocks ((t:ℂ) • (1:Mat m m)) (X-z•Y)
        ((X-z•Y)ᴴ) ((t:ℂ) • (1:Mat n n))).PosSemidef)) ∧
    (∀ m n, 1 ≤ m → 1 ≤ n → ∀ (X Y : Mat m n) (z : ℂ),
      ‖X-coef X Y • Y‖ ≤ ((1+Real.sqrt (min m n))/2)*‖X-z•Y‖) ∧
    (∀ n, 2≤n → ∃ Y : Mat n n,
      (∀ z : ℂ, 1≤‖1-z•Y‖) ∧ ‖(1:Mat n n)-coef 1 Y • Y‖=(1+Real.sqrt n)/2) ∧
    (∀ n (Y : Mat n n) (hY : Y.IsHermitian) (lo hi : ℝ), 0<lo →
      (∀ i, lo≤hY.eigenvalues i ∧ hY.eigenvalues i≤hi) →
      (∃ i, hY.eigenvalues i=lo) → (∃ j, hY.eigenvalues j=hi) →
      ‖(1:Mat n n)-((2/(lo+hi):ℝ):ℂ) • Y‖=(hi-lo)/(hi+lo) ∧
        ∀ z : ℂ, (hi-lo)/(hi+lo)≤‖(1:Mat n n)-z•Y‖) := by
  sorry
end OMA.S_mo_271853
