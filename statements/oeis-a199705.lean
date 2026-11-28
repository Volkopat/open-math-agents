import Mathlib

/-!
# OEIS A199705: Barker's g.f. and parity formulas for zero-sum triples with no equal neighbors

Source: https://oeis.org/A199705 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 09 2011), offset 1: Number of -n..n arrays x(0..2) of 3 elements with
zero sum and no two neighbors equal. The formula section states: Conjectures from Colin Barker, May
16 2018: (Start) G.f.: 2*x*(3 + x + 2*x^2) / ((1 - x)^3*(1 + x)). a(n) = n + 3*n^2 for n even.
a(n) = 2 + n + 3*n^2 for n odd. (End)

Formalization notes:
* a(n) counts the triples (x0, x1, x2) with entries in -n..n, x0 + x1 + x2 = 0, x0 /= x1 and
  x1 /= x2 (the neighbors of a 3-element array).
* `main` is the conjunction of the three conjectures. The parity formulas are stated in the
  integers for n >= 1. The g.f. is stated as A(x) = N(x) * D(x)^(-1) in Q[[x]] (D has constant term
  1, so it is invertible); the definition gives a(0) = 0 (no array for n = 0), so the series
  Sum_{n >= 0} a(n) x^n is the g.f. Sum_{n >= 1} a(n) x^n of the entry.
* Controls: the parity formulas, proved for the definition, give a(1..4) = 6, 14, 32, 52, as in
  the entry.
-/

namespace OMA.S_oeis_a199705

/-- A199705(n): zero-sum triples in `-n..n` with no two neighbors equal. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p : ℤ × ℤ × ℤ => p.1 + p.2.1 + p.2.2 = 0 ∧ p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2)).card

open PowerSeries in
/-- Barker's conjectures: the g.f., a(n) = n + 3n^2 for even n, a(n) = 2 + n + 3n^2 for odd n. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (2 * X * (3 + X + 2 * X ^ 2)) * ((1 - X) ^ 3 * (1 + X))⁻¹ ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → (a n : ℤ) = n + 3 * n ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 1 → (a n : ℤ) = 2 + n + 3 * n ^ 2) := by
  sorry

end OMA.S_oeis_a199705
