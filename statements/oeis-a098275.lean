import Mathlib

/-!
# A098275: Coefficients in a simultaneous approximation to Li(2,-1) and Li(3,-1).

Source: https://oeis.org/A098275
Credit: @rpabani

The source gives the formula
a(n) = Sum_{i=0..n} Sum_{j=0..n} C(n, i)^2*C(n, j)^2*C(n+i, n)*C(i+j, i), with offset 0,
which is used here as the definition. It reproduces the listed terms 1, 8, 264, 13040.

Conjecture (F. Chapoton, Jan 28 2026, in OEIS A098275): a(n) is divisible by n+1.

The second conjecture in the source, about a fourth root of the generating function, is a separate
statement and is not included.
-/

namespace OMA.S_oeis_a098275

/-- OEIS A098275, by the double sum formula given in the entry. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    n.choose i ^ 2 * n.choose j ^ 2 * (n + i).choose n * (i + j).choose i

theorem main : ∀ n : ℕ, (n + 1) ∣ a n := by
  sorry

end OMA.S_oeis_a098275
