import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a341723

/-- Stirling numbers of the second kind `S(n, k)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

/-- OEIS A000556: `a(n) = ∑_{k=0}^{n} k! * F(k + 1) * S(n, k)`. -/
def a000556 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.fib (k + 1) * stirling2 n k

/-- OEIS A341723: triangle `T(n, k) = (-1)^(n - k) * C(n, k) * A000556(n - k)` for `0 ≤ k ≤ n`. -/
def a341723 (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n - k) * (Nat.choose n k : ℤ) * (a000556 (n - k) : ℤ)

/-- OEIS A341723 conjectures (Mélika Tebni, Sep 09 2023):
1. For every prime `p` and `0 < k < p`, `p ∣ T(p, k)`.
2. For every `m : ℕ` and odd `k` with `0 < k < 2^m`, `2^m ∣ T(2^m, k)`. -/
theorem main :
    (∀ p k : ℕ, p.Prime → 0 < k → k < p → (p : ℤ) ∣ a341723 p k) ∧
    (∀ m k : ℕ, 0 < k → k < 2 ^ m → Odd k → ((2 ^ m : ℕ) : ℤ) ∣ a341723 (2 ^ m) k) := by
  sorry

end OMA.S_oeis_a341723
