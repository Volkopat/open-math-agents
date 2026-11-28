import Mathlib

/-!
# A114646: Let M(n) be the n X n matrix m(i,j)=min(i,j) for 1<=i,j<=n then a(n) is the trace of M(n)^(-4).

Source: https://oeis.org/A114646
Credit: @agchua

L. Edson Jeffery (Jan 21 2012), in the formula section of A114646:
  (Conjecture) G.f.: F(x)=x*(1+45*x+24*x^2)/(1-x)^2. - L. Edson Jeffery, Jan 21 2012
  (Conjecture) a(n)=2*a(n-1)-a(n-2), n>1, a(1)=1, a(2)=47. - L. Edson Jeffery, Jan 21 2012
This file states both conjectures together. The g.f. is an identity of formal power series over ℚ,
(∑ a(n) X^n) * (1 - X)^2 = X * (1 + 45X + 24X^2); the offset is 1 and the g.f. has no constant
term, and a(0) is the trace of the empty matrix, 0. The recurrence is stated with its initial values
a(1) = 1, a(2) = 47, for every n ≥ 3, where all its indices are terms (offset 1; the literal n > 1
would also involve a(0) at n = 2).
Definition: M(n) has the entries min(i, j) for 1 ≤ i, j ≤ n; with the indices i, j : Fin n counted
from 0 the entry is min(i+1, j+1). M(n) is invertible (det M(n) = 1); M(n)^(-4) is taken as the
fourth power of the inverse matrix (Matrix.inv over ℚ), which is also the inverse of M(n)^4.
-/

namespace OMA.S_oeis_a114646

/-- M(n): the n X n matrix with entries min(i, j), 1 ≤ i, j ≤ n. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => ((min ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ)

/-- A114646: a(n) = trace(M(n)^(-4)). -/
noncomputable def a (n : ℕ) : ℚ := Matrix.trace ((M n)⁻¹ ^ 4)

/-- Jeffery's conjectures: the g.f. x(1+45x+24x^2)/(1-x)^2, and a(n) = 2a(n-1) - a(n-2) with
a(1) = 1, a(2) = 47. -/
theorem main : PowerSeries.mk a * (1 - PowerSeries.X) ^ 2 =
      PowerSeries.X * (1 + 45 * PowerSeries.X + 24 * PowerSeries.X ^ 2) ∧
    (a 1 = 1 ∧ a 2 = 47 ∧ ∀ n : ℕ, 3 ≤ n → a n = 2 * a (n - 1) - a (n - 2)) := by
  sorry

end OMA.S_oeis_a114646
