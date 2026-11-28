import Mathlib

/-!
# OEIS A193438: divisibility of the coefficients of exp( Sum x^(4n+1)/(4n+1) )

Source: https://oeis.org/A193438
Credit: @sntntHb

A193438: expansion of e.g.f. `exp( Sum_{n>=0} x^(4*n+1)/(4*n+1) )`.

Conjectures stated in the OEIS entry:
- `a(n)` is divisible by `5^floor(n/5)` for `n >= 0`.
- `a(n)` is divisible by `p^floor(n/p)` for prime `p == 1 (mod 4)`.

Formalized: `F` is the power series `Sum_{n>=0} X^(4n+1)/(4n+1)` over `ℚ`, `egf` is `exp(F)`
(the exponential series substituted at `F`), and `a n = n! * [X^n] egf`. Divisibility of the
(integral) value `a n` by an integer `d` is expressed as `a n = d * m` for some integer `m`.
`main` is the conjunction of the two conjectures.
-/

namespace OMA.S_oeis_a193438

open PowerSeries

/-- `Sum_{n>=0} X^(4n+1)/(4n+1)`. -/
noncomputable def F : PowerSeries ℚ := mk fun k => if k % 4 = 1 then (1 / (k : ℚ)) else 0

/-- The e.g.f. `exp(F)`. -/
noncomputable def egf : PowerSeries ℚ := (exp ℚ).subst F

/-- `a(n) = n! * [X^n] exp(F)`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n egf

theorem main :
    (∀ n : ℕ, ∃ k : ℤ, a n = (5 : ℚ) ^ (n / 5) * k) ∧
    (∀ p : ℕ, p.Prime → p % 4 = 1 → ∀ n : ℕ, ∃ k : ℤ, a n = (p : ℚ) ^ (n / p) * k) := by
  sorry

end OMA.S_oeis_a193438
