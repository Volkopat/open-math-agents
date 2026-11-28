import Mathlib

/-!
# A081798: a(n) = Sum_{k = 0..n} C(n,k) * C(n+k,k) * C(n+2*k,k)

Source: https://oeis.org/A081798
Credit: @sntntHb

A081798 (offset 0): `a(n) = Sum_{k=0..n} C(n,k) * C(n+k,k) * C(n+2k,k)`:
1, 7, 115, 2371, 54091, 1307377, …  For example
`a(1) = C(1,0)*C(1,0)*C(1,0) + C(1,1)*C(2,1)*C(3,1) = 1 + 6 = 7`.

The entry records two conjectures (R. J. Mathar):
- `n^2*(3n-4)*a(n) - (3n-2)*(30n^2-50n+13)*a(n-1) + (9n^3-30n^2+29n-6)*a(n-2)
   - (3n-1)*(n-2)^2*a(n-3) = 0`;
- `n^2*a(n) + (-28n^2+24n-3)*a(n-1) + 3*(-19n^2+78n-77)*a(n-2) + (5n-12)*(n-3)*a(n-3)
   - 2*(n-3)^2*a(n-4) = 0`.

Formalization: the terms are computed in the integers, and each recurrence is stated for every
`n` for which all of its terms are defined (`n ≥ 3`, respectively `n ≥ 4`).
-/

namespace OMA.S_oeis_a081798

/-- `a(n) = ∑_{k=0}^{n} C(n,k) C(n+k,k) C(n+2k,k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * ((n + k).choose k : ℤ) * ((n + 2 * k).choose k : ℤ)

/-- Mathar's two conjectured recurrences. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n →
      (n : ℤ) ^ 2 * (3 * n - 4) * a n
        - (3 * (n : ℤ) - 2) * (30 * (n : ℤ) ^ 2 - 50 * n + 13) * a (n - 1)
        + (9 * (n : ℤ) ^ 3 - 30 * (n : ℤ) ^ 2 + 29 * n - 6) * a (n - 2)
        - (3 * (n : ℤ) - 1) * ((n : ℤ) - 2) ^ 2 * a (n - 3) = 0) ∧
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) ^ 2 * a n
        + (-28 * (n : ℤ) ^ 2 + 24 * n - 3) * a (n - 1)
        + 3 * (-19 * (n : ℤ) ^ 2 + 78 * n - 77) * a (n - 2)
        + (5 * (n : ℤ) - 12) * ((n : ℤ) - 3) * a (n - 3)
        - 2 * ((n : ℤ) - 3) ^ 2 * a (n - 4) = 0) := by
  sorry

end OMA.S_oeis_a081798
