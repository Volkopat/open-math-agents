import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Basic

namespace OMA.S_oeis_a227051

/-- The `(2k)`-th E.G.F. coefficient of `cos(x) - sin(x) * sinh(x)`:
`d(k) = (-1)^k - ∑_{j=0}^{k-1} (-1)^j * C(2k, 2j+1)`. -/
def denomCoeff (k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k - ∑ j ∈ Finset.range k, (-1 : ℤ) ^ j * (Nat.choose (2 * k) (2 * j + 1) : ℤ)

/-- OEIS A227051: E.G.F. `E(x) = ∑_{n ≥ 0} a(n) * x^(2n) / (2n)! = 1 / (cos(x) - sin(x) * sinh(x))`,
characterized by `a(0) = 1` and the E.G.F. product identity
`∑_{k=0}^n C(2n, 2k) * denomCoeff(k) * a(n - k) = 0` for all `n ≥ 1`.
Conjecture: `a(n) ≡ 3 (mod 10)` for all `n ≥ 1`. -/
theorem main :
    ∀ a : ℕ → ℤ, a 0 = 1 →
      (∀ n : ℕ, 1 ≤ n →
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n) (2 * k) : ℤ) * denomCoeff k * a (n - k) = 0) →
      ∀ n : ℕ, 1 ≤ n → a n ≡ 3 [ZMOD 10] := by
  sorry

end OMA.S_oeis_a227051
