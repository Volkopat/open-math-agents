import Mathlib

/-!
# A135231: Wu's recurrence and g.f. for the row sums of A103451 * A000012(signed) * A007318

Source: https://oeis.org/A135231
Credit: @ivillar

A135231 (offset 0): row sums of the triangle A135230 = A103451 * A000012(signed) * A007318;
data 1, 2, 4, 6, 12, 22, 44, 86, 172, 342, ...
Conjectures (Chai Wah Wu, Aug 31 2023):
a(n) = 2*a(n-1) + a(n-2) - 2*a(n-3) for n > 3;
G.f.: (-2*x^3 - x^2 + 1)/((x - 1)*(x + 1)*(2*x - 1)).
Equivalent conjecture: a(n) = A128209(n+1) for n > 0, where A128209 = A001045 + 1 (Jacobsthal
numbers plus 1).

Formalization notes.
* A103451 is the lower-triangular matrix with T(n,0) = T(n,n) = 1 and all other entries 0;
  A000012(signed) is the lower-triangular matrix with entries (-1)^(i-j) for j <= i; A007318
  is Pascal's matrix binomial(j, k). All three are lower triangular, so in the entry (n, k) of
  the product the inner indices run over 0..n.
* a(n) is the sum of the entries (n, k) for k = 0..n (the entries with k > n vanish).
* The g.f. identity is stated over ℤ⟦X⟧, cross-multiplied by the denominator
  (x-1)*(x+1)*(2x-1), whose constant coefficient is 1. The recurrence is stated for n > 3.
* A001045 (Jacobsthal): A001045(0) = 0, A001045(1) = 1, A001045(n) = A001045(n-1) +
  2*A001045(n-2); A128209(m) = A001045(m) + 1.
-/

namespace OMA.S_oeis_a135231

open PowerSeries

/-- A103451 as a lower-triangular matrix: T(n,0) = T(n,n) = 1, T(n,k) = 0 for 0 < k < n. -/
def A103451 (n k : ℕ) : ℤ := if k ≤ n ∧ (k = 0 ∨ k = n) then 1 else 0

/-- A000012 (signed) as a lower-triangular matrix: (1; -1, 1; 1, -1, 1; ...). -/
def S (i j : ℕ) : ℤ := if j ≤ i then (-1) ^ (i - j) else 0

/-- A135230: the entry (n, k) of A103451 * A000012(signed) * A007318. -/
def T (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), A103451 n i * S i j * (j.choose k : ℤ)

/-- A135231: the row sums of A135230. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

/-- A001045: the Jacobsthal numbers. -/
def A001045 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => A001045 (n + 1) + 2 * A001045 n

/-- Wu's conjectures: the g.f. (cross-multiplied), the recurrence for n > 3, and
a(n) = A128209(n+1) = A001045(n+1) + 1 for n > 0. -/
theorem main :
    PowerSeries.mk a * ((X - 1) * (X + 1) * (2 * X - 1) : PowerSeries ℤ) =
      -2 * X ^ 3 - X ^ 2 + 1 ∧
    (∀ n : ℕ, 3 < n → a n = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) ∧
    (∀ n : ℕ, 0 < n → a n = A001045 (n + 1) + 1) := by
  sorry

end OMA.S_oeis_a135231
