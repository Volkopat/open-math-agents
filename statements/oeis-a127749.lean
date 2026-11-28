import Mathlib

/-!
# A127749: Inverse of number triangle A(n,k) = 1/(2n+1) if k <= n <= 2k, 0 otherwise.

Source: https://oeis.org/A127749
Credit: @ShadowAlzazel

Conjectures recorded in the OEIS entry (Comments section):
  Conjectures: row sums modulo 2 are the Fredholm-Rueppel sequence A036987; row sums of
  triangle modulo 2 are A111982. Row sums are A127750.
The last sentence is a cross-reference (A127750 is defined as these row sums), not a
conjecture. Both conjectures are stated, as a conjunction. A127749, A036987 and A111982 all have
offset 0, so there is no index shift.

Formalization.
* `triangle N` is the number triangle A(n,k) = 1/(2n+1) if k ≤ n ≤ 2k, 0 otherwise, truncated to
  indices 0..N-1 (the same definition as in the merged statement of oeis-a127750). It is lower
  triangular with nonzero diagonal 1/(2n+1), so its inverse is again lower triangular and row n
  of the inverse is row n of the inverse of any truncation containing row n. The statement
  quantifies over every truncation N > n, so it does not depend on a choice of truncation size.
* `T N` is the inverse of `triangle N` (Mathlib's matrix inverse): the triangle A127749.
* First conjecture. "Row sums modulo 2" presupposes that the row sums are integers, so the first
  conjunct states that the sum of row n of `T N` is an integer m with m mod 2 = A036987(n),
  exactly as in the merged statement of oeis-a127750.
* Second conjecture. A111982 takes values 1, 1, 2, 3, 2, 4, ..., which are not residues mod 2,
  so "row sums of triangle modulo 2" is read as: reduce every entry of the triangle mod 2, then
  sum each row. This presupposes integer entries, so the second conjunct states that row n of
  `T N` consists of integers t k whose residues mod 2 (in {0, 1}) sum to A111982(n).
* A111982 is "Row sums of abs(A111967)", and A111967 is "Inverse of number triangle A101688".
  A101688 is read as a triangle in its Comments section: T(n,k) = 1 if k ≥ n/2 (0 ≤ k ≤ n), that
  is k ≤ n ≤ 2k, and 0 otherwise. `triangle101688 N` is that triangle truncated to 0..N-1, and
  `A111982 N n` is the sum of the absolute values of row n of its inverse.
* `A036987 n` is the Fredholm-Rueppel sequence (offset 0), encoded with the Formula section of
  A036987 ("a(n) = 1 iff n = 2^k - 1 for some k, 0 otherwise", M. F. Hasler).
-/

namespace OMA.S_oeis_a127749

open Matrix

/-- The number triangle `A(n,k) = 1/(2n+1)` if `k ≤ n ≤ 2k`, `0` otherwise, on indices `0..N-1`. -/
def triangle (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 / (2 * (n : ℚ) + 1) else 0

/-- A127749: the inverse of the truncation `triangle N`. -/
noncomputable def T (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := (triangle N)⁻¹

/-- A101688 read as a triangle: `1` if `k ≤ n ≤ 2k`, `0` otherwise, on indices `0..N-1`. -/
def triangle101688 (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 else 0

/-- A111982(n), the sum of the absolute values of row `n` of A111967, the inverse of A101688. -/
noncomputable def A111982 (N : ℕ) (n : Fin N) : ℚ := ∑ k, |(triangle101688 N)⁻¹ n k|

open scoped Classical in
/-- The Fredholm-Rueppel sequence A036987 (offset 0): `a(n) = 1` iff `n = 2^m - 1`, else `0`. -/
noncomputable def A036987 (n : ℕ) : ℕ := if ∃ m : ℕ, n = 2 ^ m - 1 then 1 else 0

/-- A127749 conjectures: (1) the row sums, taken mod 2, are the Fredholm-Rueppel sequence
A036987; (2) the row sums of the triangle reduced mod 2 are A111982. -/
theorem main :
    (∀ (N : ℕ) (n : Fin N), ∃ m : ℤ, ∑ k, T N n k = m ∧ m % 2 = (A036987 (n : ℕ) : ℤ)) ∧
    (∀ (N : ℕ) (n : Fin N), ∃ t : Fin N → ℤ, (∀ k, T N n k = t k) ∧
      ((∑ k, t k % 2 : ℤ) : ℚ) = A111982 N n) := by
  sorry

end OMA.S_oeis_a127749
