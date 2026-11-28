import Mathlib

/-!
# OEIS A128391: the powers of A054523 applied to Ramanujan's tau that have a zero term

Source: https://oeis.org/A128391 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Gary W. Adamson, Feb 28 2007), offset 1: A054523^24 * A000594, where A054523 is the
triangle T(n,k) = phi(n/k) if k divides n and T(n,k) = 0 otherwise, read as an infinite lower
triangular matrix, and A000594 is Ramanujan's tau. Comment: Conjecture: Given A054523^k, k = any
positive integer, zero appears only in the sequence A018391 (k=24).

Formalization notes:
* A018391 in the comment is read as A128391, the entry itself, as the parenthetical k=24 says.
* tau n is the coefficient of X ^ n in X times the product of (1 - X ^ m) ^ 24 over 1 ≤ m ≤ n.
  The generating function of A000594 is q times the product over all m ≥ 1; the factors with
  m > n do not change the coefficients of degree at most n.
* T n j is the entry of A054523 in row n and column j, with phi = Nat.totient, and app f n is the
  sum of T n j * f j over 1 ≤ j ≤ n, the product of that matrix with the column f. The k-th
  iterate of app applied to tau is A054523^k * A000594, and k = 24 gives A128391.
* main says that, for k = 1, 2, 3, ..., the sequence A054523^k * A000594 has a zero term at some
  index n ≥ 1 exactly when k = 24.
-/

namespace OMA.S_oeis_a128391

open PowerSeries

/-- Ramanujan's tau function (A000594): the coefficient of `X ^ n` in `X * ∏_{m ≥ 1} (1 - X ^ m) ^ 24`.
The factors with `m > n` do not change coefficients of degree at most `n`. -/
noncomputable def tau (n : ℕ) : ℤ :=
  coeff n ((X : PowerSeries ℤ) * ∏ m ∈ Finset.range n, (1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 24)

/-- The triangle A054523: `T n j = phi (n / j)` if `j ∣ n`, and `0` otherwise. -/
def T (n j : ℕ) : ℤ := if j ∣ n then ((n / j).totient : ℤ) else 0

/-- The product of the lower triangular matrix A054523 with a column `f` indexed from 1. -/
def app (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.Icc 1 n, T n j * f j

/-- Adamson's conjecture: among k = 1, 2, 3, ... only k = 24 gives a sequence
A054523^k * A000594 with a zero term. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ((∃ n : ℕ, 1 ≤ n ∧ (app^[k] tau) n = 0) ↔ k = 24) := by
  sorry

end OMA.S_oeis_a128391
