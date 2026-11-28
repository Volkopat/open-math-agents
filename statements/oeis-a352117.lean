import Mathlib

/-!
# OEIS A352117: Yanev and Kotesovec's series for the coefficients of the e.g.f. 1/sqrt(2 - exp(2x))

Source: https://oeis.org/A352117 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A352117 (Seiichi Manyama, Mar 05 2022), offset 0: Expansion of e.g.f. 1/sqrt(2 - exp(2*x)).
Formula section:
a(n) = Sum_{k=0..n} 2^(n-k) * (Product_{j=0..k-1} (2*j+1)) * Stirling2(n,k).
a(n) ~ 2^n * n^n / (log(2)^(n + 1/2) * exp(n)). - Vaclav Kotesovec, Mar 05 2022
Conjectural o.g.f. as a continued fraction of Stieltjes type: 1/(1 - x/(1 - 4*x/(1 - 3*x/(1 - 8*x/(1 - ... - (2*n-1)*x/(1 - 4*n*x/(1 - ... ))))))). Cf. A346982.  - Peter Bala, Aug 22 2023
For n > 0, a(n) = Sum_{k=1..n} a(n-k)*(1-k/n/2)*binomial(n,k)*2^k. - Tani Akinari, Sep 06 2023
a(0) = 1; a(n) = a(n-1) - 2*Sum_{k=1..n-1} (-2)^k * binomial(n-1,k) * a(n-k). - Seiichi Manyama, Nov 18 2023
Conjecture: a(n) = Sum_{k>=1} 2^(n - 3*k - 1/2) * k^n * binomial(2*k, k) for n > 0. - Velin Yanev and Vaclav Kotesovec, Jul 21 2026

The problem stated here is the last line, Yanev and Kotesovec's conjecture.

Formalization notes:
* The e.g.f. is the real function egf(x) = 1/sqrt(2 - exp(2x)), analytic near 0 since
  2 - exp(2x) > 0 for x < log(2)/2. a(n) is n! times its n-th Taylor coefficient at 0, that is
  its n-th derivative at 0, `iteratedDeriv n egf 0`.
* The sum over k >= 1 is written with k + 1 for k >= 0. The conjecture says that the series
  converges to a(n), so it is stated with `HasSum`, which asserts convergence and the value
  together. 2^(n - 3k - 1/2) is the real power `Real.rpow`.
* The definition reproduces the entry's data (1, 1, 5, 37, 377, 4921, ... from n = 0); the proof
  file proves all 19 listed terms as controls.
-/

namespace OMA.S_oeis_a352117

/-- The exponential generating function of A352117. -/
noncomputable def egf (x : ℝ) : ℝ := 1 / Real.sqrt (2 - Real.exp (2 * x))

/-- A352117: a(n) is n! times the coefficient of x^n in the e.g.f., its n-th derivative at 0. -/
noncomputable def a (n : ℕ) : ℝ := iteratedDeriv n egf 0

/-- Yanev and Kotesovec's conjecture. -/
theorem main : ∀ n : ℕ, 0 < n →
    HasSum (fun k : ℕ => (2 : ℝ) ^ ((n : ℝ) - 3 * ((k : ℝ) + 1) - 1 / 2) * ((k : ℝ) + 1) ^ n *
      ((2 * (k + 1)).choose (k + 1) : ℝ)) (a n) := by
  sorry

end OMA.S_oeis_a352117
