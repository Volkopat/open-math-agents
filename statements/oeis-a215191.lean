import Mathlib

/-!
# OEIS A215191: Barker's generating function and closed forms

Source: https://oeis.org/A215191 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Aug 05 2012), offset 1: Number of arrays of 4 0..n integers with no sum of
consecutive elements equal to a disjoint adjacent sum of an equal number of elements. Data: 0, 18,
88, 276, 664, ... (row 4 of the table A215190). The formula section states: Empirical: a(n) =
4*a(n-1) - 5*a(n-2) + 5*a(n-4) - 4*a(n-5) + a(n-6). Conjectures from Colin Barker, Jul 22 2018:
(Start) G.f.: 2*x^2*(9 + 8*x + 7*x^2) / ((1 - x)^5*(1 + x)). a(n) = n*(3*n^3 + n^2 - 1)/3 for
n even. a(n) = (3*n^4 + n^3 - n - 3)/3 for n odd. (End)

Formalization notes:
* An array of 4 0..n integers is a function `Fin 4 → ℕ` with every value in 0..n, x i being the
  element at position i, counted from 0. A sum of consecutive elements is the sum of the k ≥ 1
  elements at positions i, ..., i + k - 1, and the disjoint adjacent sum of an equal number of
  elements is the sum of the next k elements, at positions i + k, ..., i + 2k - 1 (a block and the
  equal block on its left are the same pair read from the other block). `good x` says that no
  such pair of blocks inside the array has equal sums. `get x m` is the element at position m,
  with the value 0 past the end, which the condition i + 2k ≤ 4 never reaches.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n. The set is finite: the
  proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^5 (1 + x) = 2x^2 (9 + 8x + 7x^2) in
  Q[[x]], which is equivalent because (1 - x)^5 (1 + x) has constant term 1. The closed forms are
  stated in the rationals, where the division by 3 is exact, for the terms n ≥ 1 of each parity.
* `main` is the conjunction of Barker's three conjectures.
* Controls proved in the proof file: a(1..34), all the entry's listed terms.
-/

namespace OMA.S_oeis_a215191

open PowerSeries

/-- The element at position m of the array x of length 4, and 0 past its end. -/
def get (x : Fin 4 → ℕ) (m : ℕ) : ℕ := if h : m < 4 then x ⟨m, h⟩ else 0

/-- No sum of k ≥ 1 consecutive elements of the array x of length 4 (positions i, ..., i + k - 1)
equals the sum of the disjoint adjacent block of the next k elements (positions i + k, ...,
i + 2k - 1). -/
def good (x : Fin 4 → ℕ) : Prop :=
  ∀ i k : ℕ, 0 < k → i + 2 * k ≤ 4 →
    ∑ t ∈ Finset.range k, get x (i + t) ≠ ∑ t ∈ Finset.range k, get x (i + k + t)

/-- A215191(n): the number of arrays of 4 integers in 0..n with no sum of consecutive elements
equal to a disjoint adjacent sum of an equal number of elements. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 4 → ℕ | (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the closed forms for even and odd n. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X)) =
      2 * X ^ 2 * (9 + 8 * X + 7 * X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → (a n : ℚ) = n * (3 * n ^ 3 + n ^ 2 - 1) / 3) ∧
    (∀ n : ℕ, n % 2 = 1 → (a n : ℚ) = (3 * n ^ 4 + n ^ 3 - n - 3) / 3) := by
  sorry

end OMA.S_oeis_a215191
