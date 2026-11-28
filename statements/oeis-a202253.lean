import Mathlib

/-!
# OEIS A202253: a(n) = 1 + 2 floor((2n^2 + 2n)/3)

Source: https://oeis.org/A202253 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 14 2011), offset 1: Number of zero-sum -n..n arrays of 3 elements with
adjacent element differences also in -n..n. Formula section: Conjecture: a(n) =
1+2*floor((2*n^2+2*n)/3). - Clark Kimberling, Apr 12 2012.

Formalization notes:
* An array is a triple (x, y, z) of integers in -n..n with x + y + z = 0 whose adjacent differences
  x - y and y - z also lie in -n..n; a(n) is the number of such triples.
* floor((2n^2 + 2n)/3) is the natural-number quotient (2n^2 + 2n) / 3.
* `main` states the formula for every n >= 1, the offset of the entry.
* Controls from the entry (proved in the proof file by kernel computation from the definition):
  a(1..4) = 3, 9, 17, 27.
-/

namespace OMA.S_oeis_a202253

open Finset

/-- The zero-sum arrays (x, y, z) of three elements of -n..n whose adjacent differences x - y and
y - z also lie in -n..n. -/
noncomputable def arrays (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter fun t =>
    t.1 + t.2.1 + t.2.2 = 0 ∧ -(n : ℤ) ≤ t.1 - t.2.1 ∧ t.1 - t.2.1 ≤ n ∧
      -(n : ℤ) ≤ t.2.1 - t.2.2 ∧ t.2.1 - t.2.2 ≤ n

/-- A202253(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Kimberling's conjecture: a(n) = 1 + 2 floor((2n^2 + 2n)/3) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 1 + 2 * ((2 * n ^ 2 + 2 * n) / 3) := by
  sorry

end OMA.S_oeis_a202253
