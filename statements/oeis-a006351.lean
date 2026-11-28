import Mathlib

/-!
# A006351: Number of series-parallel networks with n labeled edges.

Source: https://oeis.org/A006351
Credit: @thatoneguy006

The conjecture stated here, from the entry:

  Conjecture: a(n) = A379459(n-2,0) = A379460(n-1,0) for n > 1 with a(1) = 1.
  - Mikhail Kurkov, Jan 16 2025

Definitions.
* A006351 (offset 1). The entry gives its e.g.f. A(x) as the reversion of 2*log(1+x)-x,
  equivalently A(0) = 0 and A'(x) = (1 + A)/(1 - A) (Kruchinin, Bala). Comparing coefficients in
  A'(1 - A) = 1 + A gives a(1) = 1 and, for m >= 1,
  a(m+1) = a(m) + Sum_{k=1..m} C(m,k) a(k) a(m+1-k),
  which is the definition used here (with a(0) = 0, the constant term). It reproduces the data
  1, 2, 8, 52, 472, 5504, 78416, ... of the entry.
* A379459 (array, n, k >= 0): A(0,k) = 2*(k+1)! and
  A(n,k) = A(n-1,k+1) + 2*(k+1)!*Sum_{j=0..k} A(n-1,j)/j!, computed in ℚ (the division by j! is
  exact). Rows: 2, 4, 12, 48, ...; 8, 36, 192, 1200, ...; 52, 368, 2880, ...
* A379460 (array, n, k >= 0): A(0,k) = 1, A(n,0) = A(n-1,0) + A(n-1,1), and
  A(n,k) = A(n,k-1) + (k+1)*(A(n-1,k) + A(n-1,k+1)) for k >= 1.
  Rows: 1, 1, 1, ...; 2, 6, 12, 20, ...; 8, 44, 140, 340, ...
-/

namespace OMA.S_oeis_a006351

/-- A006351, by the coefficient recurrence of `A'(1 - A) = 1 + A`, with `a 0 = 0`, `a 1 = 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a (n + 1) +
      ∑ k : Fin (n + 1), (n + 1).choose (k.val + 1) * a (k.val + 1) * a (n + 1 - k.val)

/-- The array A379459. -/
def A379459 : ℕ → ℕ → ℚ
  | 0, k => 2 * ((k + 1).factorial : ℚ)
  | n + 1, k => A379459 n (k + 1) +
      2 * ((k + 1).factorial : ℚ) *
        ∑ j ∈ Finset.range (k + 1), A379459 n j / (j.factorial : ℚ)

/-- The array A379460. -/
def A379460 : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, 0 => A379460 n 0 + A379460 n 1
  | n + 1, k + 1 => A379460 (n + 1) k + (k + 2) * (A379460 n (k + 1) + A379460 n (k + 2))

/-- Kurkov's conjecture: `a(n) = A379459(n-2,0) = A379460(n-1,0)` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n →
    A379459 (n - 2) 0 = (a n : ℚ) ∧ A379460 (n - 1) 0 = a n := by
  sorry

end OMA.S_oeis_a006351
