import Mathlib

/-!
# A396722: a(n) = (4^n/2) * p(n, 5/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1.

Source: https://oeis.org/A396722 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (Clark Kimberling, Jun 06 2026; name edited by Peter Munn, Jun 21 2026), offset 0:
a(n) = (4^n/2) * p(n, 5/2), where p(n,x) is the Lagrange interpolating polynomial through
(1,0) and (k,1) for k = 2..n+1. Terms: 0, 3, 9, 34, 133, 526, 2090, 8324, ...
The formula section states:

  Conjecture D-finite with recurrence n*a(n) +2*(-4*n+5)*a(n-1) +8*(2*n-5)*a(n-2)=0.
  - R. J. Mathar, Jun 30 2026

A comment by Eiver Rodríguez (Sep 28 2026) gives a short proof of this recurrence from the
interpolation conditions.

Formalization notes:
* `p n` is Mathlib's `Lagrange.interpolate` over ℚ on the index set `Finset.range (n + 1)`, with
  node `i + 1` for index `i` (so the nodes are 1, 2, ..., n+1) and value 0 at index 0 (node 1)
  and 1 at every other index (nodes 2..n+1). The nodes are distinct, so this is the unique
  polynomial of degree ≤ n through the n+1 given points, as in the entry's Mathematica program
  (`InterpolatingPolynomial[{0, 1, ..., 1}, x]`). For n = 0 it is the constant 0.
* `a n` is computed in ℚ (the entry's values are integers).
* The source gives no range. The recurrence mentions a(n-2), so it is stated for n ≥ 2, where all
  three terms exist. Coefficients are written in ℚ, with no natural-number subtraction in them.
* Controls: p(1,x) = x - 1, so a(1) = 2 * (3/2) = 3; at n = 2 the recurrence reads
  2*9 - 6*3 + 8*(-1)*0 = 0, with a(0..2) = 0, 3, 9 from the entry.
-/

namespace OMA.S_oeis_a396722

open Polynomial

/-- p(n, x): the Lagrange interpolating polynomial through (1, 0) and (k, 1) for k = 2..n+1.
Index `i ∈ {0, ..., n}` has node `i + 1`; the value is 0 at index 0 and 1 elsewhere. -/
noncomputable def p (n : ℕ) : ℚ[X] :=
  Lagrange.interpolate (Finset.range (n + 1)) (fun i : ℕ => (i : ℚ) + 1)
    (fun i : ℕ => if i = 0 then (0 : ℚ) else 1)

/-- A396722: a(n) = (4^n/2) * p(n, 5/2). -/
noncomputable def a (n : ℕ) : ℚ := 4 ^ n / 2 * (p n).eval (5 / 2)

/-- Mathar's conjectured recurrence, for n ≥ 2. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (n : ℚ) * a n + 2 * (-4 * (n : ℚ) + 5) * a (n - 1) + 8 * (2 * (n : ℚ) - 5) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a396722
