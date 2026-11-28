import Mathlib

/-!
# OEIS A233402: Barker's g.f. and closed form for (n+1) X 2 arrays with monotone sums, no equal neighbors

Source: https://oeis.org/A233402 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A233402 (R. H. Hardin, Dec 09 2013), offset 1: Number of (n+1) X (1+1) 0..2 arrays with row
and column sums nondecreasing, and no adjacent elements equal.
Formula section:
Empirical: a(n) = 3*a(n-2) - 3*a(n-4) + a(n-6).
Conjectures from Colin Barker, Oct 11 2018: (Start)
G.f.: x*(9 + 11*x - 5*x^2 - 9*x^3 + 2*x^4 + 3*x^5) / ((1 - x)^3*(1 + x)^3).
a(n) = (62 - 14*(-1)^n + (50-6*(-1)^n)*n + (11+(-1)^(1+n))*n^2) / 16.
(End)

Formalization notes:
* An array is a function f : Fin (n + 1) -> Fin 2 -> Fin 3, f i j the entry in row i and column j.
  Row sums nondecreasing: the sum of row i is at most the sum of row i + 1. Column sums
  nondecreasing: the sum of column j is at most the sum of column j + 1 (here column 0 against
  column 1). No adjacent elements equal: horizontally adjacent entries (same row, consecutive
  columns) and vertically adjacent entries (same column, consecutive rows) differ. All sums are
  taken over the natural numbers 0..2. This reading reproduces the entry's data (9, 11, 22, 24,
  41, 42, 66, 65, ... for n = 1..20 by direct enumeration).
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^3 (1 + x)^3 = x(9 + 11x - 5x^2 - 9x^3 + 2x^4 + 3x^5) in the formal power series ring
  over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the closed form for every n >= 1 as an identity of rationals.
* Controls proved in the proof file: the definition gives 9, 11, 22, 24, 41, 42 for n = 1..6.
-/

namespace OMA.S_oeis_a233402

open PowerSeries Finset

/-- Row sums nondecreasing down the rows, column sums nondecreasing across the columns, and no two
horizontally or vertically adjacent elements equal (f i j: row i, column j). -/
def good {n : ℕ} (f : Fin (n + 1) → Fin 2 → Fin 3) : Prop :=
  (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      (f i 0).val + (f i 1).val ≤ (f i' 0).val + (f i' 1).val) ∧
    (∀ j j' : Fin 2, j'.val = j.val + 1 → ∑ i, (f i j).val ≤ ∑ i, (f i j').val) ∧
    (∀ i (j j' : Fin 2), j'.val = j.val + 1 → f i j ≠ f i j') ∧
    (∀ (i i' : Fin (n + 1)) j, i'.val = i.val + 1 → f i j ≠ f i' j)

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A233402: the number of (n+1) X (1+1) 0..2 arrays with row and column sums nondecreasing, and no
adjacent elements equal. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter good).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 + X) ^ 3) = X * (9 + 11 * X - 5 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (62 - 14 * (-1) ^ n + (50 - 6 * (-1) ^ n) * n + (11 + (-1) ^ (1 + n)) * n ^ 2) / 16 := by
  sorry

end OMA.S_oeis_a233402
