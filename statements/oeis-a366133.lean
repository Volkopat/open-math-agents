import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a366133

/-- Signed Stirling numbers of the first kind `s(n, k)`. -/
def stirling1 : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling1 n k - (n : ℤ) * stirling1 n (k + 1)

/-- OEIS A005444: `a(n) = ∑_{k=0}^{n} k! * F(k + 1) * s(n, k)`. -/
def a005444 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (k.factorial : ℤ) * (Nat.fib (k + 1) : ℤ) * stirling1 n k

/-- OEIS A366133: triangle `T(n, k) = C(n, k) * A005444(n - k)` for `0 ≤ k ≤ n`. -/
def a366133 (n k : ℕ) : ℤ :=
  (Nat.choose n k : ℤ) * a005444 (n - k)

/-- OEIS A366133 conjectures:
1. For every prime `p` and `0 < k < p`, `p ∣ T(p, k)`.
2. For every `m : ℕ` and odd `k` with `0 < k < 2^m`, `2^m ∣ T(2^m, k)`. -/
theorem main :
    (∀ p k : ℕ, p.Prime → 0 < k → k < p → (p : ℤ) ∣ a366133 p k) ∧
    (∀ m k : ℕ, 0 < k → k < 2 ^ m → Odd k → ((2 ^ m : ℕ) : ℤ) ∣ a366133 (2 ^ m) k) := by
  sorry

end OMA.S_oeis_a366133
