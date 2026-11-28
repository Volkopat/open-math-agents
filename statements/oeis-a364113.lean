import Mathlib

/-!
# The two supercongruences for every row of Bala's Legendre array

Source: https://oeis.org/A364113
Credit: @DomTheDeveloper

Peter Bala defines T(R,n) as the coefficient of x^n in
P_n((1+x)/(1-x))^R/(1-x). Put y=x/(1-x). The coefficient of y^j in
P_n(1+2y) is (n choose j) * (n+j choose j), and the coefficient of x^n
in y^j/(1-x) is n choose j. These two identities give `row` below.
-/

namespace OMA.S_oeis_a364113

noncomputable def row (R n : ℕ) : ℕ :=
  let L : Polynomial ℕ := ∑ j ∈ Finset.range (n + 1),
    Polynomial.monomial j (n.choose j * (n + j).choose j)
  ∑ j ∈ Finset.range (n + 1), n.choose j * (L ^ R).coeff j

theorem main : ∀ (R p m r : ℕ), p.Prime → 5 ≤ p → 0 < m → 0 < r →
    Nat.ModEq (p ^ (3 * r)) (row R (m * p ^ r)) (row R (m * p ^ (r - 1))) ∧
    Nat.ModEq (p ^ (3 * r)) (row R (m * p ^ r - 1)) (row R (m * p ^ (r - 1) - 1)) := by
  sorry

end OMA.S_oeis_a364113
