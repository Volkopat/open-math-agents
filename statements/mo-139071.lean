import Mathlib

/-!
# An alternating polynomial is the Vandermonde product times a symmetric polynomial

Source: https://mathoverflow.net/questions/139071 (zen-dev, MathOverflow 2013, CC BY-SA 3.0).
Credit: @connoranderson

We use the signed-permutation definition of antisymmetry and allow any integral
domain of characteristic different from two. This includes the classical statement
over the integers. In characteristic two the signed-permutation definition would
also include the constant polynomial one.
-/

namespace OMA.S_mo_139071

open MvPolynomial

theorem main : ∀ {R : Type*} [CommRing R] [IsDomain R], (2 : R) ≠ 0 →
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) R),
    (∀ σ : Equiv.Perm (Fin n), rename σ p = σ.sign • p) →
    ∃ q : MvPolynomial (Fin n) R, q.IsSymmetric ∧
      p = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (X j - X i)) * q := by
  sorry

end OMA.S_mo_139071
