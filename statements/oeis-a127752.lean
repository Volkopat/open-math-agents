import Mathlib

/-!
# A127752: Row sums of inverse of number triangle A(n,k) = 1/(3n+1) if k <= n <= 2k, 0 otherwise.

Source: https://oeis.org/A127752
Credit: @ShadowAlzazel

Conjecture recorded in the OEIS entry:
  a(n) mod 2 is first Feigenbaum symbolic sequence A035263 (conjecture). The conjecture is true at least up to 2048 first terms. (But please note the different indexing, here 0-based.)
OEIS A127752 is indexed from 0; A035263 is indexed from 1 (the A127752 entry warns about this).
So the claim is: for every n ≥ 0, a(n) ≡ A035263(n+1) (mod 2).

Formalization.
* `triangle N` is the number triangle A(n,k) = 1/(3n+1) if k ≤ n ≤ 2k, 0 otherwise, truncated to
  indices 0..N-1 (rows and columns). The infinite triangle is lower triangular with nonzero
  diagonal 1/(3n+1), so its inverse is again lower triangular and row n of the inverse is row n
  of the inverse of any truncation containing row n. The statement quantifies over every such
  truncation N > n, so it does not depend on a choice of truncation size.
* `a N n` is the n-th row sum of `(triangle N)⁻¹` (Mathlib's matrix inverse): the OEIS a(n).
* `A035263 n` = A000035(A001511(n)): the parity of the ruler function A001511(n), the exponent of
  the highest power of 2 dividing 2n (formula given in OEIS A035263, offset 1).
* `a(n) mod 2` presupposes that a(n) is an integer, so `main` states that the row sum is an
  integer m with m mod 2 = A035263(n+1).
-/

namespace OMA.S_oeis_a127752

open Matrix

/-- The number triangle `A(n,k) = 1/(3n+1)` if `k ≤ n ≤ 2k`, `0` otherwise, on indices `0..N-1`. -/
def triangle (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 / (3 * (n : ℚ) + 1) else 0

/-- Row `n` sum of the inverse of the truncation `triangle N` (for `n < N`): the OEIS `a(n)`. -/
noncomputable def a (N : ℕ) (n : Fin N) : ℚ := ∑ k, (triangle N)⁻¹ n k

/-- A035263 (offset 1): `A000035(A001511(n))`, the parity of the exponent of 2 in `2n`. -/
def A035263 (n : ℕ) : ℕ := padicValNat 2 (2 * n) % 2

/-- A127752 conjecture: the row sums of the inverse triangle, taken mod 2, are A035263
(shifted by one for the different offsets). -/
theorem main : ∀ (N : ℕ) (n : Fin N),
    ∃ m : ℤ, a N n = m ∧ m % 2 = (A035263 ((n : ℕ) + 1) : ℤ) := by
  sorry

end OMA.S_oeis_a127752
