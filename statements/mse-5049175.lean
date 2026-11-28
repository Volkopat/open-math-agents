import Mathlib

/-!
# GCDs of Faulhaber polynomials

Source: https://math.stackexchange.com/questions/5049175
Let `f_n` be the `n`-th Faulhaber polynomial, `f_n(x) = ∑_{k=1}^{x} k^n`. Conjecture (asker,
checked for `n, m < 1000`): for `n ≠ m`, `n, m > 1`, the only exception being `{n, m} = {9, 10}`
(where `gcd(f₉, f₁₀) = x(x+1)(x²+x-1)`), `gcd(f_n, f_m)` is `f₃` if `n, m` are both odd, `f₂`
if both are even, and `f₁` otherwise.

Conventions. Polynomials are in `ℚ[X]` and gcds are taken up to units (`Associated`).
`f_n = (B_{n+1}(X + 1) - B_{n+1}(0)) / (n + 1)` with Mathlib's Bernoulli polynomials, which
agrees with `∑_{k=1}^{x} k^n` at every natural `x` for `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_5049175

open Polynomial

/-- The Faulhaber polynomial `f_n`. -/
noncomputable def f (n : ℕ) : ℚ[X] :=
  (1 / ((n : ℚ) + 1)) • ((Polynomial.bernoulli (n + 1)).comp (X + 1) - C ((Polynomial.bernoulli (n + 1)).eval 0))

theorem main :
    ∀ n m : ℕ, 1 < n → 1 < m → n ≠ m → ¬ (n = 9 ∧ m = 10) → ¬ (n = 10 ∧ m = 9) →
      Associated (gcd (f n) (f m))
        (if Odd n ∧ Odd m then f 3 else if Even n ∧ Even m then f 2 else f 1) := by
  sorry

end OMA.S_mse_5049175
