import Mathlib

/-!
# A284641: Expansion of (Sum_{k>=0} x^(k^2*(k+1)^2/4))^12.

Source: https://oeis.org/A284641
Credit: @luciusacarr

a(n) is the number of ways to write n as an ordered sum of 12 squares of triangular numbers
(A000537: 0, 1, 9, 36, 100, ..., also the partial sums of cubes).

The entry's comments record two conjectures. `main` states both, as a conjunction, in the order
the source gives them.

Conjecture: a(n) > 0 for all n.
Extended conjecture: every number is the sum of at most 12 squares of triangular numbers (or
partial sums of cubes).

Reading of the source:
* The squares of triangular numbers are `(k(k+1)/2)^2 = k^2(k+1)^2/4` for `k ≥ 0` (0 included,
  as in the generating function). a(n) > 0 says `n` is a sum of exactly 12 of them, in some order.
* "Sum of at most 12" means a sum of `r ≤ 12` such numbers, repetitions allowed (summands indexed
  by `Fin r`).
* Checked numerically for every n ≤ 30000.
-/

namespace OMA.S_oeis_a284641

/-- `m` is the square of a triangular number (A000537), 0 included. -/
def IsTriangularSquare (m : ℕ) : Prop := ∃ k : ℕ, m = k ^ 2 * (k + 1) ^ 2 / 4

theorem main :
    -- a(n) > 0: every n is a sum of 12 squares of triangular numbers.
    (∀ n : ℕ, ∃ b : Fin 12 → ℕ, (∀ i, IsTriangularSquare (b i)) ∧ ∑ i, b i = n) ∧
    -- Every number is the sum of at most 12 squares of triangular numbers.
    (∀ n : ℕ, ∃ (r : ℕ) (b : Fin r → ℕ), r ≤ 12 ∧
      (∀ i, IsTriangularSquare (b i)) ∧ ∑ i, b i = n) := by
  sorry

end OMA.S_oeis_a284641
