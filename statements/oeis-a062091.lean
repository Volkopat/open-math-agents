import Mathlib

/-!
# A062091: a(1) = 2, a(n) = smallest even number which does not divide the product of all previous terms.

Source: https://oeis.org/A062091 (conjecture by R. J. Mathar, Jul 08 2025)

Conjecture: a(n) = 2*A062090(n-1) for n >= 3, where A062090 is defined by
A062090(1) = 1, A062090(n) = smallest odd number that does not divide the product of all
previous terms.

Conventions. Both sequences have offset 1. In A062091 smallest even number means smallest
positive even number (the number 0 never divides a nonzero product, so it has to be excluded
for the definition to give the listed terms 2, 4, 6, 10, 14, ...). A smallest element is
taken with `sInf` on `ℕ`; the relevant sets are always nonempty.

The products of the first `n` terms are carried along: `aProd n` is the product
`a(1) * ... * a(n)` (with `aProd 0 = 1`), and for `n >= 2` the term `a n` is the least positive
even number not dividing `aProd (n - 1)`; likewise `bProd` and `b` for A062090.
-/

namespace OMA.S_oeis_a062091

/-- The least odd number not dividing `p`. -/
noncomputable def oddNext (p : ℕ) : ℕ := sInf {m : ℕ | Odd m ∧ ¬ m ∣ p}

/-- `bProd n` is the product of the first `n` terms of A062090. -/
noncomputable def bProd : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => bProd (n + 1) * oddNext (bProd (n + 1))

/-- A062090 (offset 1): `b 1 = 1`, and `b n` is the least odd number not dividing the
product of the previous terms. -/
noncomputable def b (n : ℕ) : ℕ := if n ≤ 1 then 1 else oddNext (bProd (n - 1))

/-- The least positive even number not dividing `p`. -/
noncomputable def evenNext (p : ℕ) : ℕ := sInf {m : ℕ | Even m ∧ 0 < m ∧ ¬ m ∣ p}

/-- `aProd n` is the product of the first `n` terms of A062091. -/
noncomputable def aProd : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => aProd (n + 1) * evenNext (aProd (n + 1))

/-- A062091 (offset 1): `a 1 = 2`, and `a n` is the least positive even number not dividing
the product of the previous terms. -/
noncomputable def a (n : ℕ) : ℕ := if n ≤ 1 then 2 else evenNext (aProd (n - 1))

theorem main : ∀ n : ℕ, 3 ≤ n → a n = 2 * b (n - 1) := by
  sorry

end OMA.S_oeis_a062091
