import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a023864

open Finset PowerSeries

/-- `A023864(n) = ∑_{i=1}^{⌊(n+1)/2⌋} i * F(n + 2 - i)` for `n ≥ 1`, and `A023864(0) = 0`,
where `F = Nat.fib` (so `t(j) = F(j + 1)` gives `t = (F(2), F(3), F(4), ...)`). -/
def a023864 (n : ℕ) : ℤ :=
  if n = 0 then 0
  else ∑ i ∈ Icc 1 ((n + 1) / 2), (i : ℤ) * (Nat.fib (n + 2 - i) : ℤ)

/-- OEIS A023864 conjecture (Maksym Voznyy, Jul 27 2009):
the generating function `A(X) = ∑_{n≥0} a(n) X^n` satisfies
`((1 - X - X^2) * (1 - X^2 - X^4)^2) * A(X) = X + X^2 + 2*X^3 + X^6`,
i.e., `A(X) = X*(-1 - X - 2*X^2 - X^5) / ((X^2 + X - 1) * (X^4 + X^2 - 1)^2)`. -/
theorem main :
    ((1 - X - X ^ 2) * (1 - X ^ 2 - X ^ 4) ^ 2 : PowerSeries ℤ) *
        PowerSeries.mk a023864 =
      X + X ^ 2 + 2 * X ^ 3 + X ^ 6 := by
  sorry

end OMA.S_oeis_a023864
