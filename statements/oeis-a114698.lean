import Mathlib

/-!
# A114698: a conjectured generating function and recurrence

Source: https://oeis.org/A114698
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. The g.f. (1)
follows from the formula of the entry, which is used as the definition here. The recurrence (2) is
false as stated at n = 2 (in its own indexing a(0) = 1, a(1) = 18, a(2) = 38, and 38 ≠ 2*18 - 1);
`main` contains the corrected recurrence (n ≥ 3), which is proved.

A114698 (offset 1): let M(n) be the n X n matrix m(i,j) = min(i,j) for 1 <= i,j <= n; then a(n) is the
trace of M(n)^(-3);
data 1, 18, 38, 58, 78, 98, 118, 138, 158, 178, 198, 218, ...

Conjectures (L. Edson Jeffery, Jan 21 2012), written with the terms renumbered from 0:
(1) G.f.: F(x) = (1+16*x+3*x^2)/(1-x)^2.
(2) a(n) = 2*a(n-1) - a(n-2), n>1, a(0)=1, a(1)=18.

Formalization: the entry records a(1) = 1 and a(n) = 20n - 22 for n ≥ 2 (offset 1), and this formula,
with values in ℤ, is the definition of a(n) used here (the value of the Lean expression at n = 0 is
not used). The conjectures number the terms from 0, so their k-th term is a(k+1). Accordingly (1) is
stated as the identity (Sum_k a(k+1) x^k) * (1 - x)^2 = 1 + 16*x + 3*x^2 of formal power series over ℚ,
and the corrected (2) as a(k+1) = 2*a(k) - a(k-1) for k ≥ 3. `main` is the conjunction of the two.
-/

namespace OMA.S_oeis_a114698

open PowerSeries

/-- a(1) = 1 and a(n) = 20n - 22 for n ≥ 2, the formula recorded in the entry. -/
def a (n : ℕ) : ℤ := if n = 1 then 1 else 20 * (n : ℤ) - 22

/-- The conjectured g.f. and the corrected recurrence (k ≥ 3) for A114698, terms numbered from 0. -/
theorem main :
    (PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * (1 - X) ^ 2 = 1 + 16 * X + 3 * X ^ 2) ∧
    (∀ k : ℕ, 3 ≤ k → a (k + 1) = 2 * a k - a (k - 1)) := by
  sorry

end OMA.S_oeis_a114698
