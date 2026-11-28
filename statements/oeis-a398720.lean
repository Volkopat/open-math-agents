import Mathlib

/-!
# A398720: Triangle read by rows: T(n,k) in which the n-th row lists the weight distribution of
square Single Parity Check Product (SPCP) [(n+1)^2, n^2, 4] code, 0 <= k <= n*floor(n/2).

Source: https://oeis.org/A398720
Credit: @bnb9001

As the entry notes, T(n,k) is the number of n X n matrices with exactly 2k 1's such that there
are an even number of 1's in every row and column (offset 0: 1, 1, 1, 0, 1, 1, 0, 9, 6, 1, ...).
Matrices are functions `Fin n -> Fin n -> Bool`, with `true` for a 1.

Conjecture: T(n, n*(n-1)/2) = n! for n odd. Andrew R. Epstein notes that the conjecture holds: the
complement of such a matrix has n ones and odd row and column sums, so it is a permutation matrix.
-/

namespace OMA.S_oeis_a398720

open Finset

/-- Number of ones in row `i`. -/
def rowOnes {n : ℕ} (M : Fin n → Fin n → Bool) (i : Fin n) : ℕ :=
  (univ.filter fun j => M i j = true).card

/-- Number of ones in column `j`. -/
def colOnes {n : ℕ} (M : Fin n → Fin n → Bool) (j : Fin n) : ℕ :=
  (univ.filter fun i => M i j = true).card

/-- Total number of ones. -/
def totOnes {n : ℕ} (M : Fin n → Fin n → Bool) : ℕ :=
  (univ.filter fun p : Fin n × Fin n => M p.1 p.2 = true).card

/-- A398720: `T(n, k)` counts `n × n` 0/1 matrices with `2k` ones and every row and column even. -/
def T (n k : ℕ) : ℕ :=
  (univ.filter fun M : Fin n → Fin n → Bool =>
    totOnes M = 2 * k ∧ (∀ i, Even (rowOnes M i)) ∧ ∀ j, Even (colOnes M j)).card

/-- The conjecture, proved: `T(n, n(n-1)/2) = n!` for odd `n`. -/
theorem main : ∀ n : ℕ, Odd n → T n (n * (n - 1) / 2) = n.factorial := by
  sorry

end OMA.S_oeis_a398720
