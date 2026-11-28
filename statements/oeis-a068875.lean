import Mathlib

/-!
# A068875: Vertical-line zero conjecture for power-series polynomials of (1 + x*C)*C

Source: https://oeis.org/A068875
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A068875: Expansion of (1 + x*C)*C, where C = (1 - (1 - 4*x)^(1/2))/(2*x) is the g.f.
for Catalan numbers, A000108.

Statement:
If A(x)^t = 1 + 2*t*x + Sum_{n >= 2} t*P(n,t)*x^n, then we conjecture that all the zeros of
the polynomial P(n,t) lie on the vertical line Re(t) = -n/2 in the complex plane.

Conventions:
- Since `C(x) = 1 + x*C(x)^2`, `(1 + x*C(x))*C(x) = C(x) + x*C(x)^2 = 2*C(x) - 1`, so
  `a(0) = 1` and `a(n) = 2*C(n)` for `n >= 1`, where `C(n) = catalan n`.
- For `t ∈ ℂ`, `A(x)^t = exp(t * log(A(x)))` has coefficient `c(n, t)` of `x^n`, defined
  recursively from the formal power series `A(x) = 1 + Sum_{n>=1} 2*C(n)*x^n` via
  `n * c(n, t) = Sum_{k=1..n} (k * (t + 1) - n) * a(k) * c(n - k, t)` with `c(0, t) = 1`.
- For `n >= 2`, `P(n, t) = c(n, t) / t`, equivalently `c(n, t) = t * P(n, t)`. So the zeros of
  `P(n, ·)` are the nonzero zeros of `c(n, ·)`, together with `t = 0` exactly when
  `∂c(n, t)/∂t` vanishes at `0`; as `-n/2 ≠ 0`, the conjecture requires that derivative to be
  nonzero, and `main` states both parts.
-/

namespace OMA.S_oeis_a068875

/-- The `n`-th term of OEIS A068875: `a(0) = 1`, `a(n) = 2 * catalan n` for `n >= 1`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else 2 * catalan n

/-- The `n`-th coefficient `[x^n] A(x)^t` as a function of `t : ℂ`, via the J.C.P. Miller
    recurrence `n * c(n, t) = Sum_{k=1..n} (k*(t+1) - n) * a(k) * c(n-k, t)`. -/
noncomputable def coeffPow (t : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
    (1 / ((n + 1 : ℂ))) *
      ∑ j : Fin (n + 1),
        ((((j.1 + 1 : ℕ) : ℂ) * (t + 1) - (n + 1 : ℂ)) * (a (j.1 + 1) : ℂ) *
          coeffPow t (n - j.1))
  decreasing_by omega

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      deriv (fun t : ℂ => coeffPow t n) 0 ≠ 0 ∧
      ∀ t : ℂ, t ≠ 0 → coeffPow t n = 0 → t.re = -((n : ℝ) / 2) := by
  sorry

end OMA.S_oeis_a068875
