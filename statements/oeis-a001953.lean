import Mathlib

/-!
# A001953: a(n) = floor((n + 1/2) * sqrt(2)).

Source: https://oeis.org/A001953
Credit: @luciusacarr

The entry records the conjecture (Clark Kimberling, Oct 05 2014):
Let s(n) = zeta(3) - Sum_{k = 1..n} 1/k^3. Conjecture: for n >= 1, s(a(n)) < 1/n^2 < s(a(n)-1),
and the difference sequence of A049473 consists solely of 0's and 1's, in positions given by the
nonhomogeneous Beatty sequences A001954 and A001953, respectively.

Reading of the source:
* `a(n) = floor((n + 1/2) * sqrt(2))` for `n ≥ 0` (natural-number floor of a positive real).
* `zeta(3)` is the Riemann zeta value, taken as the real part of `riemannZeta 3` (which is real),
  and `s(n) = zeta(3) - Sum_{k=1..n} 1/k^3` is the tail of the zeta(3) series after n terms.
* This file states the first assertion of the conjecture: for every `n ≥ 1`,
  `s(a(n)) < 1/n^2` and `1/n^2 < s(a(n) - 1)`. (The second assertion, about the difference
  sequence of A049473, is a separate claim and is not part of this statement.)
-/

namespace OMA.S_oeis_a001953

/-- A001953: `a(n) = floor((n + 1/2) * sqrt(2))`. -/
noncomputable def a (n : ℕ) : ℕ := ⌊((n : ℝ) + 1 / 2) * Real.sqrt 2⌋₊

/-- `s(n) = zeta(3) - Sum_{k=1..n} 1/k^3`. -/
noncomputable def s (n : ℕ) : ℝ :=
  (riemannZeta 3).re - ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 3

theorem main :
    ∀ n : ℕ, 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1) := by
  sorry

end OMA.S_oeis_a001953
