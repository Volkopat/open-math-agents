import Mathlib

/-!
# OEIS A067274: integer-root quadratics with small coefficients

Source: https://oeis.org/A067274 (OEIS Foundation, CC BY-SA 4.0).

`a(n)` is the number of ordered integer pairs `(b, c)` with `-n ≤ b ≤ n` and `-n ≤ c ≤ n` such
that both roots of `x^2 + b x + c = 0` are integers. Offset 0; the data begins
`1, 4, 10, 16, 25, 31, 41, ...`.

Conjecture (OEIS comment): the difference `a(n) - a(n-1)` is `6` if and only if `n` is a prime
number. A later comment says that it is a corollary of Jovovic's formula
`a(n) = a(n-1) + 2 (τ(n) + 1) + [n is a square]` for `n > 1`.

Formalization notes:
* Both roots of the monic quadratic `x^2 + b x + c` are integers exactly when it factors as
  `(x - r)(x - s)` with `r, s ∈ ℤ`, that is `b = -(r + s)` and `c = r s` (`IntRoots b c`).
  A double root is allowed; non-real roots are not integers.
* The difference is taken in `ℤ`, for every `n ≥ 1` (the conjecture's range).
-/

namespace OMA.S_oeis_a067274

/-- Both roots of `x^2 + b x + c` are integers: it factors as `(x - r)(x - s)` over `ℤ`. -/
def IntRoots (b c : ℤ) : Prop := ∃ r s : ℤ, b = -(r + s) ∧ c = r * s

open Classical in
/-- A067274(n): the number of ordered pairs `(b, c)` with `-n ≤ b ≤ n` and `-n ≤ c ≤ n` such
that both roots of `x^2 + b x + c = 0` are integers. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter (fun p => IntRoots p.1 p.2)).card

/-- The difference `a(n) - a(n-1)` is `6` exactly when `n` is prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ((a n : ℤ) - a (n - 1) = 6 ↔ n.Prime) := by
  sorry

end OMA.S_oeis_a067274
