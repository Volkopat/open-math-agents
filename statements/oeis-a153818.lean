import Mathlib

/-!
# A153818: a(n) = Sum_{k=1..n} floor(n^2/k^2) (Cloitre's error-term conjecture)

Source: https://oeis.org/A153818 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A153818 (offset 1): a(n) = Sum_{k=1..n} floor(n^2/k^2); data 1, 5, 12, 22, 35, 53, 72, ...

The entry records (Benoit Cloitre, Jan 22 2013):

  Asymptotic formula: a(n) = zeta(2)*n^2 + zeta(1/2)*n + O(n^(1/2)).
  Conjecture: a(n) = zeta(2)*n^2 + zeta(1/2)*n + O(n^0.5/log(n)) (see link).

Only the second line, the conjecture, is stated here.

Reading of the source:
* `a n = ∑_{k=1}^{n} ⌊n^2 / k^2⌋`, computed in `ℕ` (natural division is the floor).
* `zeta(2)` and `zeta(1/2)` are values of the Riemann zeta function, Mathlib's `riemannZeta`,
  which is real at real arguments; the statement uses their real parts. (`zeta(1/2) < 0` is the
  analytically continued value, as in the source's asymptotic formula.)
* `O(n^0.5/log(n))` is a big-O as `n → ∞` over the naturals: the error
  `a(n) - zeta(2) n^2 - zeta(1/2) n` is `O(√n / log n)`.
-/

namespace OMA.S_oeis_a153818

open Asymptotics Filter

/-- A153818(n) = ∑_{k=1}^{n} ⌊n^2 / k^2⌋. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, n ^ 2 / k ^ 2

/-- Cloitre's conjecture: `a(n) = ζ(2) n^2 + ζ(1/2) n + O(√n / log n)`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ) - (riemannZeta 2).re * (n : ℝ) ^ 2 - (riemannZeta (1 / 2)).re * n)
      =O[atTop] (fun n : ℕ => Real.sqrt n / Real.log n) := by
  sorry

end OMA.S_oeis_a153818
