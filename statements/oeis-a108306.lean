import Mathlib

/-!
# A108306: Expansion of (3*x+1)/(1-3*x-3*x^2).

Source: https://oeis.org/A108306 (conjecture in the comments of the entry)

The comment: the sequence is the INVERT transform of (1, 5, 10, 20, 40, 80, 160, ...) and can
be obtained by extracting the upper left terms of matrix powers of [(1,5); (1,2)]. These results
are a case (a=5, b=2) of the conjecture: the INVERT transform of a sequence starting
(1, a, a*b, a*b^2, a*b^3, ...) is equivalent to extracting the upper left terms of powers of the
2x2 matrix [(1,a); (1,b)].

Conventions:
* `s a b` is the sequence (1, a, a*b, a*b^2, ...) indexed from 1: `s a b 1 = 1` and
  `s a b (k + 2) = a * b ^ k` (the value at 0 is unused).
* `invert f` is the INVERT transform, defined by `1 + Sum_(n >= 1) t(n) x^n =
  1/(1 - Sum_(k >= 1) f(k) x^k)`, i.e. `t 0 = 1` and `t n = Sum_(k = 1..n) f(k) * t(n - k)`
  for `n >= 1`. The transform consists of the terms `t n` for `n >= 1`.
* The general conjecture is stated for all integers `a, b` and all `n >= 1`: `t n` equals the
  upper left entry (index `0 0`) of the `n`-th power of the matrix `!![1, a; 1, b]`.
* The particular case: `A` is the power series `(1 + 3 x) / (1 - 3 x - 3 x^2)` over `ℚ` (the
  inverse exists since the constant term is `1`), with offset 0. Its first term
  `a(0) = 1` is the first term `t 1` of the INVERT transform, so the case `a = 5, b = 2` reads
  `a(n) = t (n + 1) = (M ^ (n + 1)) 0 0` for every `n >= 0`.
-/

namespace OMA.S_oeis_a108306

open PowerSeries

/-- The sequence (1, a, a*b, a*b^2, ...) indexed from 1. -/
def s (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => a * b ^ k

/-- The INVERT transform: `t 0 = 1`, `t (n + 1) = Sum_(k = 0..n) f(k + 1) * t(n - k)`. -/
def invert (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), f (k + 1) * invert f (n - k)
decreasing_by omega

/-- The matrix [(1,a); (1,b)]. -/
def M (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, a; 1, b]

/-- The generating function `(1 + 3 x) / (1 - 3 x - 3 x^2)` of A108306. -/
noncomputable def A : PowerSeries ℚ := (1 + 3 * X) * (1 - 3 * X - 3 * X ^ 2)⁻¹

theorem main :
    (∀ a b : ℤ, ∀ n : ℕ, 1 ≤ n → invert (s a b) n = (M a b ^ n) 0 0) ∧
    (∀ n : ℕ, coeff n A = (invert (s 5 2) (n + 1) : ℚ) ∧
      coeff n A = ((M 5 2 ^ (n + 1)) 0 0 : ℚ)) := by
  sorry

end OMA.S_oeis_a108306
