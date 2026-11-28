import Mathlib

/-!
# OEIS A193437: divisibility of the coefficients of exp( Sum x^(3n+1)/(3n+1) )

Source: https://oeis.org/A193437
Credit: @sntntHb

A193437: expansion of e.g.f. `exp( Sum_{n>=0} x^(3*n+1)/(3*n+1) )`.

Conjectures stated in the OEIS entry:
- `a(n)` is divisible by `7^floor(n/7)` for `n >= 0`.
- `a(n)` is divisible by `p^floor(n/p)` for prime `p == 1 (mod 3)`.

Formalized: `F` is the power series `Sum_{n>=0} X^(3n+1)/(3n+1)` over `ℚ`, `egf` is `exp(F)`
(the exponential series substituted at `F`), and `a n = n! * [X^n] egf`. Divisibility of the
(integral) value `a n` by an integer `d` is expressed as `a n = d * m` for some integer `m`.
`main` is the conjunction of the two conjectures.
-/

namespace OMA.S_oeis_a193437

open PowerSeries

/-- `Sum_{n>=0} X^(3n+1)/(3n+1)`. -/
noncomputable def F : PowerSeries ℚ := mk fun k => if k % 3 = 1 then (1 / (k : ℚ)) else 0

/-- The e.g.f. `exp(F)`. -/
noncomputable def egf : PowerSeries ℚ := (exp ℚ).subst F

/-- `a(n) = n! * [X^n] exp(F)`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n egf

theorem main :
    (∀ n : ℕ, ∃ k : ℤ, a n = (7 : ℚ) ^ (n / 7) * k) ∧
    (∀ p : ℕ, p.Prime → p % 3 = 1 → ∀ n : ℕ, ∃ k : ℤ, a n = (p : ℚ) ^ (n / p) * k) := by
  sorry

end OMA.S_oeis_a193437
