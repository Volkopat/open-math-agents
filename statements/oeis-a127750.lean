import Mathlib

/-!
# A127750: Row sums of inverse of number triangle A(n,k) = 1/(2n+1) if k <= n <= 2k, 0 otherwise.

Source: https://oeis.org/A127750
Credit: @ShadowAlzazel

Conjecture recorded in the OEIS entry:
  a(n) mod 2 gives Fredholm-Rueppel sequence A036987. The conjecture is true at least up to n=2048.
Both OEIS A127750 and A036987 are indexed from 0, so there is no index shift:
the claim is: for every n ≥ 0, a(n) ≡ A036987(n) (mod 2).

Formalization.
* `triangle N` is the number triangle A(n,k) = 1/(2n+1) if k ≤ n ≤ 2k, 0 otherwise, truncated to
  indices 0..N-1 (rows and columns). The infinite triangle is lower triangular with nonzero
  diagonal 1/(2n+1), so its inverse is again lower triangular and row n of the inverse is row n
  of the inverse of any truncation containing row n. The statement quantifies over every such
  truncation N > n, so it does not depend on a choice of truncation size.
* `a N n` is the n-th row sum of `(triangle N)⁻¹` (Mathlib's matrix inverse): the OEIS a(n).
* `A036987 n` is the Fredholm-Rueppel sequence (offset 0). The OEIS name of A036987 is just
  "Fredholm-Rueppel sequence"; it is encoded here with the Formula section of A036987
  ("a(n) = 1 iff n = 2^k - 1 for some k, 0 otherwise", M. F. Hasler), which agrees with its
  data 1, 1, 0, 1, 0, 0, 0, 1, ... and its cross-reference "Characteristic function of A000225".
* `a(n) mod 2` presupposes that a(n) is an integer, so `main` states that the row sum is an
  integer m with m mod 2 = A036987(n).
-/

namespace OMA.S_oeis_a127750

open Matrix

/-- The number triangle `A(n,k) = 1/(2n+1)` if `k ≤ n ≤ 2k`, `0` otherwise, on indices `0..N-1`. -/
def triangle (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 / (2 * (n : ℚ) + 1) else 0

/-- Row `n` sum of the inverse of the truncation `triangle N` (for `n < N`): the OEIS `a(n)`. -/
noncomputable def a (N : ℕ) (n : Fin N) : ℚ := ∑ k, (triangle N)⁻¹ n k

open scoped Classical in
/-- The Fredholm-Rueppel sequence A036987 (offset 0): `a(n) = 1` iff `n = 2^m - 1`, else `0`. -/
noncomputable def A036987 (n : ℕ) : ℕ := if ∃ m : ℕ, n = 2 ^ m - 1 then 1 else 0

/-- A127750 conjecture: the row sums of the inverse triangle, taken mod 2, are the
Fredholm-Rueppel sequence A036987 (both indexed from 0). -/
theorem main : ∀ (N : ℕ) (n : Fin N),
    ∃ m : ℤ, a N n = m ∧ m % 2 = (A036987 (n : ℕ) : ℤ) := by
  sorry

end OMA.S_oeis_a127750
