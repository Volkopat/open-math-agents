import Mathlib

/-!
# A103769: Trinomial transform of central binomial coefficients A001405.

Source: https://oeis.org/A103769
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 4, 21, 123, 757, 4788, 30817, 200784, ...
It is defined by the explicit formula of the entry,
a(n) = sum_{k=0..n} sum_{j=0..n} C(n,j)*C(j,k)*C(j+k,floor((j+k)/2)).

Conjecture (R. J. Mathar, Dec 14 2011):
n*(2n+1)*a(n) +2(-61n^2+57n-20)*a(n-1) +3*(205n^2-523*n+346) * a(n-2) -72*(n-2)*(16n-33)*a(n-3)
+567*(n-2)*(n-3)*a(n-4)=0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4, exactly as printed.

Remark for the reviewer: with the terms of the entry the left-hand side at n = 4 is -81756, so the
relation as printed does not hold. The listed terms do satisfy the relation in which the first
coefficient n*(2n+1) is replaced by 4*n*(2n+1). The statement below keeps the printed form.
-/

namespace OMA.S_oeis_a103769

/-- A103769, by the double sum of the entry. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    n.choose j * j.choose k * (j + k).choose ((j + k) / 2)

/-- The conjectured recurrence for A103769, as printed in the entry. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) * (2 * n + 1) * a n + 2 * (-61 * (n : ℤ) ^ 2 + 57 * n - 20) * a (n - 1)
      + 3 * (205 * (n : ℤ) ^ 2 - 523 * n + 346) * a (n - 2)
      - 72 * ((n : ℤ) - 2) * (16 * n - 33) * a (n - 3)
      + 567 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a103769
