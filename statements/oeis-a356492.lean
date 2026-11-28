import Mathlib

/-!
# A356492: Determinant of a symmetric Toeplitz matrix whose first row consists of prime(n), prime(n-1), ..., prime(1).

Source: https://oeis.org/A356492
Credit: @bnb9001

The sequence has offset 0 (1, 2, 5, 51, 264, 19532, -11904, ...). `M(n)` is the `n × n`
symmetric Toeplitz matrix with first row prime(n), prime(n-1), ..., prime(1), so its entry in row
`i`, column `j` is prime(n - |i - j|), that is `Nat.nth Nat.Prime (n - 1 - |i - j|)` with
Mathlib's 0-indexed `Nat.nth`. The determinant is an integer and can be negative; a(n) is prime
when it equals a (positive) prime number.

Conjecture: a(n) is prime only for n = 1 and 2. Robert Israel notes that the conjecture is true.
-/

namespace OMA.S_oeis_a356492

/-- The symmetric Toeplitz matrix whose first row is `prime(n), prime(n-1), ..., prime(1)`. -/
noncomputable def toep (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (Nat.nth Nat.Prime (n - 1 - Int.natAbs ((i : ℤ) - j)) : ℤ)

/-- A356492: the determinant of `toep n`. -/
noncomputable def a (n : ℕ) : ℤ := (toep n).det

/-- `a n` is a prime number exactly when `n = 1` or `n = 2`. -/
theorem main : ∀ n : ℕ, (∃ p : ℕ, p.Prime ∧ a n = p) ↔ n = 1 ∨ n = 2 := by
  sorry

end OMA.S_oeis_a356492
