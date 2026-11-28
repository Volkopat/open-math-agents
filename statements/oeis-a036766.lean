import Mathlib

/-!
# Mathar's bounded-outdegree tree recurrence (OEIS A036766)

Source: https://oeis.org/A036766
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A036/A036766.seq
Credit: @Heart-galaxy

A036766 has offset0 and counts ordered rooted trees with n non-root nodes
and every outdegree at most4. The source gives the algebraic generating
function A=1+X*A+X^2*A^2+X^3*A^3+X^4*A^4 and also the PARI construction
whose a(n) is coefficient n+1 of serreverse(X/polcyclo(5)).
We implement that independent canonical construction exactly. q=1+X+...+X^4,
F=X/q, and Y is F's compositional inverse with constant coefficient0.
Then A=q(Y) and a(n) is coefficient n of A. The companion proof verifies
X*A=Y, the source algebraic equation, constant coefficient1, and the
coefficient-n versus coefficient-(n+1) equivalence for the reversion.
The rational coefficients represent the source values exactly.

Mathar's August4,2015 fifth-order recurrence is the entry's sole marked
conjecture. Every n>=5 is retained so all preceding offset-zero indices
are valid. The numerical coefficient346618 in the a(n-2) term is split
across two source lines as34661 followed by8*n^3; it is joined without
altering the source expression. Prior literature resolution and mathematical
novelty are unverified and are not claimed.
-/

namespace OMA.S_oeis_a036766

noncomputable def q : Polynomial ℚ := 1+Polynomial.X+Polynomial.X^2+Polynomial.X^3+Polynomial.X^4

noncomputable def qs : PowerSeries ℚ := (q : PowerSeries ℚ)

noncomputable def F : PowerSeries ℚ := PowerSeries.X*qs⁻¹

noncomputable def Y : PowerSeries ℚ := F.substInvOfIsUnit (by
  have h : PowerSeries.coeff 1 F = 1 := by simp [F,qs,q]
  rw [h]
  exact isUnit_one)

noncomputable def ev (p : Polynomial ℚ) : PowerSeries ℚ := Polynomial.aeval Y p

noncomputable def A : PowerSeries ℚ := ev q

noncomputable def a (n : ℕ) : ℚ := PowerSeries.coeff n A

theorem main : ∀ n : ℕ, 5 ≤ n →
    -3*(3*(n : ℚ)+2)*(133*(n : ℚ)-347)*(3*(n : ℚ)+4)*((n : ℚ)+1)*a n +
      (111457*(n : ℚ)^4-364730*(n : ℚ)^3+228995*(n : ℚ)^2+19310*(n : ℚ)-33312)*a (n-1) +
      5*(-68503*(n : ℚ)^4+346618*(n : ℚ)^3-590627*(n : ℚ)^2+397748*(n : ℚ)-90564)*a (n-2) -
      25*((n : ℚ)-2)*(1933*(n : ℚ)^3-9435*(n : ℚ)^2+14354*(n : ℚ)-7518)*a (n-3) -
      125*((n : ℚ)-2)*((n : ℚ)-3)*(1333*(n : ℚ)^2-4384*(n : ℚ)+2718)*a (n-4) -
      625*(733*(n : ℚ)-400)*((n : ℚ)-2)*((n : ℚ)-3)*((n : ℚ)-4)*a (n-5) = 0 := by
  sorry

end OMA.S_oeis_a036766
