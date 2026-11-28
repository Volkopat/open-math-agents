import Mathlib.Data.Nat.Totient
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a126156

/-- `IsA126156 a` asserts that `a : ℕ → ℤ` is OEIS A126156, the sequence of coefficients of
`x^(2*n) / (2*n)!` in the exponential generating function `sqrt(sec(sqrt(2)*x))`,
uniquely characterized by `a 0 = 1` and the Cauchy-product identity
`A(x)^2 * cos(sqrt(2)*x) = 1`, where `cos(sqrt(2)*x) = ∑_{k≥0} (-2)^k * x^(2*k) / (2*k)!`. -/
def IsA126156 (a : ℕ → ℤ) : Prop :=
  a 0 = 1 ∧
    ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n) (2 * k) : ℤ) * (-2 : ℤ) ^ k *
          (∑ j ∈ Finset.range (n - k + 1),
            (Nat.choose (2 * (n - k)) (2 * j) : ℤ) * a j * a (n - k - j)) = 0

/-- Peter Bala's conjecture (OEIS A126156, Mar 01 2026):
the sequence `{a(n)}` reduced modulo a positive integer `k` is eventually periodic
with period dividing `φ(k)` (equivalently `a(n + φ(k)) ≡ a(n) (mod k)` for all
sufficiently large `n`). -/
theorem main :
    ∀ a : ℕ → ℤ, IsA126156 a →
      ∀ k : ℕ, 1 ≤ k →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [ZMOD (k : ℤ)] := by
  sorry

end OMA.S_oeis_a126156
