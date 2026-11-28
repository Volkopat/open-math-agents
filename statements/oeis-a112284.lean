import Mathlib

namespace OMA.S_oeis_a112284

/-- For `n ≥ 1`, `IsRowA112283 n a` means `a : ℕ → ℤ` gives the coefficients of a formal power
series `A(x) = ∑ m, a(m) x^m` with `a(0) = 1` and `1 ≤ a(m) ≤ n` for all `m ≥ 1`, such that
`A(x) = B(x)^n` for some formal power series `B(x) = ∑ m, b(m) x^m` over `ℤ` with `b(0) = 1`. -/
def IsRowA112283 (n : ℕ) (a : ℕ → ℤ) : Prop :=
  a 0 = 1 ∧ (∀ m : ℕ, 1 ≤ m → 1 ≤ a m ∧ a m ≤ (n : ℤ)) ∧
  ∃ B : PowerSeries ℤ, PowerSeries.constantCoeff B = 1 ∧
    ∀ m : ℕ, PowerSeries.coeff m (B ^ n) = a m

/-- OEIS A112284 (`A112283(n) / n`): Conjecture that `A112283(n) = n` (i.e., the first index
`m ≥ 1` with `a(m) = 1` is `m = n`, so `A112284(n) = 1`) if and only if `n = 1`, `n` is prime,
or `n = p^2` for an odd prime `p`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∀ a : ℕ → ℤ, IsRowA112283 n a →
        ((a n = 1 ∧ ∀ m : ℕ, 1 ≤ m → m < n → a m ≠ 1) ↔
          (n = 1 ∨ Nat.Prime n ∨ ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ n = p ^ 2)) := by
  sorry

end OMA.S_oeis_a112284
