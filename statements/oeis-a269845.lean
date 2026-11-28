import Mathlib

/-!
# A269845: Irregular triangle T(n,k) = (k/2+1/2)^2 if k odd, otherwise (n-k/2)^2

Source: https://oeis.org/A269845 (conjectures in the comments of the entry)

Entry (offset 1): irregular triangle read by rows: T(n,k) = (k/2+1/2)^2 if k is odd, otherwise
T(n,k) = (n-k/2)^2, where n >= 1, k = 0..2*n-1.
Conjectures: (i) Odd terms of row sum/2 is A100157. (ii) Even terms of row sum/2 is A258582.

Conventions:
* `T n k` is computed in ℕ: for odd k, k/2 + 1/2 = (k+1)/2; for even k <= 2n - 2, n - k/2 is a
  natural number.
* `rowSum n` is the sum of row n, i.e. of T(n,k) for k = 0..2n-1.
* The odd terms of the sequence n ↦ rowSum(n)/2 are those with odd index n = 2m-1 (m >= 1), and
  the even terms those with even index n = 2m (m >= 1, the rows start at n = 1).
* A100157 (offset 1, structured rhombic dodecahedral numbers, vertex structure 9) is given by its
  formula a(m) = (16m^3 - 12m^2 + 2m)/6; A258582 (offset 0) is its title
  a(m) = m(2m+1)(4m+1)/3. Divisions are exact.
-/

namespace OMA.S_oeis_a269845

/-- T(n,k) of A269845. -/
def T (n k : ℕ) : ℕ := if k % 2 = 1 then ((k + 1) / 2) ^ 2 else (n - k / 2) ^ 2

/-- The sum of row n of the triangle. -/
def rowSum (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n), T n k

/-- A100157(m) = (16m^3 - 12m^2 + 2m)/6. -/
def A100157 (m : ℕ) : ℕ := (16 * m ^ 3 - 12 * m ^ 2 + 2 * m) / 6

/-- A258582(m) = m(2m+1)(4m+1)/3. -/
def A258582 (m : ℕ) : ℕ := m * (2 * m + 1) * (4 * m + 1) / 3

theorem main :
    (∀ m : ℕ, 1 ≤ m → rowSum (2 * m - 1) / 2 = A100157 m) ∧
    (∀ m : ℕ, 1 ≤ m → rowSum (2 * m) / 2 = A258582 m) := by
  sorry

end OMA.S_oeis_a269845
