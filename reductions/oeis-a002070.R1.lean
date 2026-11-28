import OMAStatements.S_oeis_a002070
import Mathlib

/-! A002070 split into the elementary evaluation of the triple sum and the point count.

For a prime `p`, `gcd(f(x, y), p)` is `p` or `1`, and `A023900(p) = 1 - p`, `A023900(1) = 1`,
so the triple sum collapses to `p - N(p)` with `N(p)` the number of `(x, y) ∈ [1, p]^2` with
`p ∣ x^3 - x^2 - y^2 - y`, the affine points of `y^2 + y = x^3 - x^2` over `F_p`. That is `H1`.

`H2` says the coefficient of `x^p` in `x ∏ (1 - x^k)^2 (1 - x^(11k))^2` is `p - N(p)`: the
Eichler-Shimura relation `a_p = p + 1 - #E(F_p)` for the modular curve `X_1(11)`, the deep part.
-/

namespace OMA.R_oeis_a002070_R1

open OMA.S_oeis_a002070

/-- The triple sum is `p` minus the number of affine points of `y^2 + y = x^3 - x^2` mod `p`. -/
def H1 : Prop := ∀ p : ℕ, p.Prime →
    S p = (p : ℚ) - (((Finset.Icc 1 p ×ˢ Finset.Icc 1 p).filter
      (fun xy : ℕ × ℕ => (p : ℤ) ∣ f xy.1 xy.2)).card : ℚ)

/-- Eichler-Shimura for `X_1(11)`: the eta-product coefficient at `p` is `p - N(p)`. -/
def H2 : Prop := ∀ p : ℕ, p.Prime →
    (coeffAt p : ℚ) = (p : ℚ) - (((Finset.Icc 1 p ×ˢ Finset.Icc 1 p).filter
      (fun xy : ℕ × ℕ => (p : ℤ) ∣ f xy.1 xy.2)).card : ℚ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002070.main := by
  intro h1 h2 p hp
  rw [h1 p hp, h2 p hp]

end OMA.R_oeis_a002070_R1
