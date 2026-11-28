import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a205810

/-- Rescaled Chebyshev polynomials `t(n, x) = 2 * T_n(x / 2)` over `ℤ`:
`t(0, x) = 2`, `t(1, x) = x`, `t(n + 2, x) = x * t(n + 1, x) - t(n, x)`. -/
noncomputable def chebT2 : ℕ → Polynomial ℤ
  | 0 => 2
  | 1 => Polynomial.X
  | n + 2 => Polynomial.X * chebT2 (n + 1) - chebT2 n

/-- Row polynomial `R(n, x) = x^n * t(n, 1 + x + 1/x)` of OEIS A205810 (Whitney numbers of
Lucas lattices, AlSukaiti and Chbili, Proposition 2.1). -/
noncomputable def rowPolyA205810 (n : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.C ((chebT2 n).coeff j) * Polynomial.X ^ (n - j) *
      (1 + Polynomial.X + Polynomial.X ^ 2) ^ j

/-- OEIS A205810: Whitney numbers `c(n, k) = [x^k] R(n, x)` for `0 ≤ k ≤ 2n`. -/
noncomputable def a205810 (n k : ℕ) : ℤ :=
  (rowPolyA205810 n).coeff k

/-- OEIS A205810 conjecture (Peter Bala, Jun 26 2025):
For every `n ≥ 1`, `t(n, x + 1) = ∑_{k=0}^{n} c(n, n - k) * t(k, x) - c(n, n)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (chebT2 n).comp (Polynomial.X + 1) =
        (∑ k ∈ Finset.range (n + 1), Polynomial.C (a205810 n (n - k)) * chebT2 k) -
          Polynomial.C (a205810 n n) := by
  sorry

end OMA.S_oeis_a205810
