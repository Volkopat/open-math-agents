import Mathlib

/-!
# A189450: Number of 2 X n array permutations with each element moving zero or one space horizontally or diagonally.

Source: https://oeis.org/A189450
Credit: @bmendonca3

[Lean proof of this statement](https://github.com/bmendonca3/open-math-agents/blob/73df85bbef281090c2e091bf03b0cb4d1cb568cb/proofs/oeis-a189450.lean)

Entry A189450 (R. H. Hardin, Apr 22 2011), offset 1, data 1, 5, 16, 61, 225, 841, 3136, 11705, ...
Formula section:
Conjectures from Colin Barker, May 02 2018:
G.f.: x*(1 + x - 4*x^2 + x^3) / ((1 - x)*(1 + x)*(1 - 4*x + x^2)).
a(n) = ((2-sqrt(3))^(n+1) + (2+sqrt(3))^(n+1) + 8) / 12 for n even.
a(n) = (-2+(2-sqrt(3))^(1+n) + (2+sqrt(3))^(1+n)) / 12 for n odd.

`main` is the conjunction of the three conjectures.

Formalization notes:
* The cells of the 2 X n array are the pairs (i, j) in `Fin 2 × Fin n` (row i, column j). An array
  permutation is a permutation σ of the cells: the element in cell p moves to cell σ p.
* Each element moves zero or one space horizontally or diagonally: for every cell p, the cell σ p
  is p itself, or the cell next to p in the same row (horizontal), or the cell next to p on the
  diagonal, that is (i, j) and (i + 1, j + 1). The sequence is defined from this count, not from
  any of the conjectured formulas.
* Reading of the word diagonally. In this family of entries (the rows of A189449) one diagonal
  direction is meant, and the other direction has its own word, antidiagonally. The data settle
  the reading: with one diagonal direction the count is 1, 5, 16, 61 for n = 1..4, the data of the
  entry, and with both directions the count for n = 2 is 9, not 5. A vertical move is not allowed.
  The other diagonal direction alone gives the same numbers (exchange the two rows).
* G.f.: the offset is 1, so A(x) = Sum_{n >= 1} a(n) x^n has constant term 0. The quotient is
  stated as the identity A(x) * ((1 - x)(1 + x)(1 - 4x + x^2)) = x(1 + x - 4x^2 + x^3) in the
  formal power series ring over the rationals. This is the same claim, because the denominator has
  constant term 1 and is invertible.
* Closed forms: stated in the reals for every n >= 1 of the given parity, with the expressions as
  the source writes them.
-/

namespace OMA.S_oeis_a189450

open PowerSeries

/-- `Step p q`: the cell `q` is the cell `p`, or it is one space from `p` horizontally (same row,
adjacent column) or diagonally (the cells `(i, j)` and `(i + 1, j + 1)`). -/
def Step {n : ℕ} (p q : Fin 2 × Fin n) : Prop :=
  p = q ∨
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
  (p.1.val + 1 = q.1.val ∧ p.2.val + 1 = q.2.val) ∨
  (q.1.val + 1 = p.1.val ∧ q.2.val + 1 = p.2.val)

instance {n : ℕ} : DecidableRel (Step (n := n)) := fun p q => by unfold Step; infer_instance

/-- A189450: the number of permutations of the cells of the 2 X n array with each element moving
zero or one space horizontally or diagonally. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin 2 × Fin n))).filter (fun σ => ∀ p, Step p (σ p))).card

/-- Barker's conjectures: the g.f. and the closed forms for even and for odd n. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) * (1 + X) * (1 - 4 * X + X ^ 2)) =
      X * (1 + X - 4 * X ^ 2 + X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℝ) =
      ((2 - Real.sqrt 3) ^ (n + 1) + (2 + Real.sqrt 3) ^ (n + 1) + 8) / 12) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℝ) =
      (-2 + (2 - Real.sqrt 3) ^ (1 + n) + (2 + Real.sqrt 3) ^ (1 + n)) / 12) := by
  sorry

end OMA.S_oeis_a189450
