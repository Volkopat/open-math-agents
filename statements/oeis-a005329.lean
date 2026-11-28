import Mathlib

/-!
# OEIS A005329: 2-factorials as an inverse binomial transform

Source: https://oeis.org/A005329
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`A005329(n) = ∏_{i=1}^{n} (2^i - 1)`. Conjecture (OEIS entry): A005329 is the inverse binomial
transform of A075272.

Conventions:
* The BinomialMean transform is `BM(b)(n) = 2^(-n) ∑_{k=0}^{n} C(n, k) b(k)`. A075271 is defined
  by `b(0) = 1` and `BM(b)(n) = 2 b(n-1)` for `n ≥ 1`, i.e.
  `b(n) = 2^(n+1) b(n-1) - ∑_{k<n} C(n, k) b(k)`; A075272 is `BM(A075271)`, i.e. `1` at `0` and
  `2 b(n-1)` at `n ≥ 1`.
* The inverse binomial transform of `c` is `n ↦ ∑_{k=0}^{n} (-1)^(n-k) C(n, k) c(k)`.
-/

namespace OMA.S_oeis_a005329

/-- A075271. -/
def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 ^ (n + 2) * b n - ∑ k : Fin (n + 1), ((n + 1).choose k : ℤ) * b k
decreasing_by all_goals (first | omega | (have := k.isLt; omega))

/-- A075272 = BM(A075271). -/
def c : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 * b n

/-- A005329. -/
def a (n : ℕ) : ℤ := ∏ i ∈ Finset.Icc 1 n, (2 ^ i - 1)

/-- A005329 is the inverse binomial transform of A075272. -/
theorem main : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * c k := by
  sorry

end OMA.S_oeis_a005329
