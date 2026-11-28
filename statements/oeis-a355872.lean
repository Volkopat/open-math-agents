import Mathlib

/-!
# OEIS A355872: `x = ∑_{n=-∞}^∞ (-x)^(n^2) * A(x)^((n-1)^2)`

Source: https://oeis.org/A355872 (OEIS Foundation, CC BY-SA 4.0).
Here `A(x) = ∑_{k ≥ 1} a(k) * x^(4*k - 3)` satisfies
`x = ∑_{n=-∞}^∞ (-x)^(n^2) * A(x)^((n-1)^2)`.
Splitting `n = 0` (`A(x)`), `n = 1` (`-x`), `n = 2` (`x^4 * A(x)`), `n ≥ 3`, and `n = -m` (`m ≥ 1`):
`A(x) = 2*x - x^4 * A(x) - ∑_{n ≥ 3} (-x)^(n^2) * A(x)^((n-1)^2) - ∑_{m ≥ 1} (-x)^(m^2) * A(x)^((m+1)^2)`.

Conjectures (Paul D. Hanna, OEIS A355872):
1. `a(k) ≡ 2 (mod 4)` for all `k ≥ 1`.
2. `a(2*k - 1) ≡ 2 (mod 8)` for all `k ≥ 1`.
3. `a(2*k) ≡ 6 (mod 8)` for all `k ≥ 1`.
(In fact `a(k) ≡ 2 * (-1)^(k - 1) (mod 16)` for all `k ≥ 1`.)
-/

namespace OMA.S_oeis_a355872

/-- Functional equation for OEIS A355872 (`A(0) = 0`):
`A(x) = 2*x - x^4*A(x) - ∑_{n ≥ 3} (-x)^(n^2)*A(x)^((n-1)^2) - ∑_{m ≥ 1} (-x)^(m^2)*A(x)^((m+1)^2)`.
For coefficient `r`, terms with `n > r` or `m > r` have `x`-power `> r` and vanish. -/
def SatisfiesA355872 (A : PowerSeries ℤ) : Prop :=
  A.coeff 0 = 0 ∧
  ∀ r : ℕ,
    A.coeff r =
      (if r = 1 then (2 : ℤ) else 0) -
      (PowerSeries.X ^ 4 * A).coeff r -
      (∑ n ∈ Finset.Icc 3 r, ((-PowerSeries.X) ^ (n ^ 2) * A ^ ((n - 1) ^ 2)).coeff r) -
      (∑ m ∈ Finset.Icc 1 r, ((-PowerSeries.X) ^ (m ^ 2) * A ^ ((m + 1) ^ 2)).coeff r)

/-- Conjectures (OEIS A355872):
There exists `A : PowerSeries ℤ` satisfying the A355872 functional equation, and for every
such `A`, defining `a(k) = A.coeff (4 * k - 3)` for `k ≥ 1`, we have:
1. `a(k) % 4 = 2` for all `k ≥ 1`,
2. `a(2 * k - 1) % 8 = 2` for all `k ≥ 1`,
3. `a(2 * k) % 8 = 6` for all `k ≥ 1`
(and in fact `a(k) ≡ 2 * (-1)^(k - 1) [ZMOD 16]`). -/
theorem main :
    (∃ A : PowerSeries ℤ, SatisfiesA355872 A) ∧
    (∀ A : PowerSeries ℤ, SatisfiesA355872 A →
      ∀ k : ℕ, 1 ≤ k →
        A.coeff (4 * k - 3) % 4 = 2 ∧
        A.coeff (4 * (2 * k - 1) - 3) % 8 = 2 ∧
        A.coeff (4 * (2 * k) - 3) % 8 = 6 ∧
        A.coeff (4 * k - 3) ≡ 2 * (-1 : ℤ) ^ (k - 1) [ZMOD 16]) := by
  sorry

end OMA.S_oeis_a355872
