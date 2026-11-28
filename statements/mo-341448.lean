import Mathlib

/-!
# Irreducibility of the triangular sum of bivariate monomials

Source: MarkoR, https://mathoverflow.net/questions/341448 (CC BY-SA 4.0).
Credit: @connoranderson

The indices are nonnegative and satisfy a+b ≤ n. The positive values of n
are intended: at degree zero the polynomial is the unit 1.
-/

namespace OMA.S_mo_341448
open MvPolynomial

noncomputable def triangular (n : ℕ) : MvPolynomial (Fin 2) ℤ :=
  ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n-a+1),
    (X 0)^a * (X 1)^b

theorem main : ∀ n : ℕ, 0 < n → Irreducible (triangular n) := by
  sorry

end OMA.S_mo_341448
