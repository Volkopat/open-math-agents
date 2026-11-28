import Mathlib

/-!
# OEIS A128392: the powers of A126988 applied to Ramanujan's tau that have a zero term

Source: https://oeis.org/A128392 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Gary W. Adamson, Feb 28 2007), offset 1: A126988^12 * A000594, where A126988 is the
triangle T(n,k) = n/k if k divides n and T(n,k) = 0 otherwise, read as an infinite lower
triangular matrix, and A000594 is Ramanujan's tau. Comment: Conjecture: Given A126988^k, k any
positive integer, A128392 is the only sequence in the infinite set with zeros.

Formalization notes:
* tau n is the coefficient of X ^ n in X times the product of (1 - X ^ m) ^ 24 over 1 ≤ m ≤ n.
  The generating function of A000594 is q times the product over all m ≥ 1; the factors with
  m > n do not change the coefficients of degree at most n.
* T n j is the entry of A126988 in row n and column j, and app f n is the sum of T n j * f j over
  1 ≤ j ≤ n, the product of that matrix with the column f. The k-th iterate of app applied to tau
  is A126988^k * A000594, and k = 12 gives A128392.
* The infinite set is formed by these sequences for k = 1, 2, 3, ...; a sequence has zeros when it
  has a zero term at some index n ≥ 1. main says that exactly k = 12 gives a sequence with zeros.
-/

namespace OMA.S_oeis_a128392

open PowerSeries

/-- Ramanujan's tau function (A000594): the coefficient of `X ^ n` in `X * ∏_{m ≥ 1} (1 - X ^ m) ^ 24`.
The factors with `m > n` do not change coefficients of degree at most `n`. -/
noncomputable def tau (n : ℕ) : ℤ :=
  coeff n ((X : PowerSeries ℤ) * ∏ m ∈ Finset.range n, (1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 24)

/-- The triangle A126988: `T n j = n / j` if `j ∣ n`, and `0` otherwise. -/
def T (n j : ℕ) : ℤ := if j ∣ n then ((n / j : ℕ) : ℤ) else 0

/-- The product of the lower triangular matrix A126988 with a column `f` indexed from 1. -/
def app (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.Icc 1 n, T n j * f j

/-- Adamson's conjecture: among k = 1, 2, 3, ... only k = 12 gives a sequence
A126988^k * A000594 with a zero term. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ((∃ n : ℕ, 1 ≤ n ∧ (app^[k] tau) n = 0) ↔ k = 12) := by
  sorry

end OMA.S_oeis_a128392
