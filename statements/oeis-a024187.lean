import Mathlib

/-!
# A024187: n-th elementary symmetric function of 3,4,...,n+3.

Source: https://oeis.org/A024187 (conjecture by Ralf Stephan, Dec 30 2004:
essentially the same as A001711)

`a(n)` (offset 1) is the `n`-th elementary symmetric function of the `n+1` numbers
`3, 4, ..., n+3`, i.e. the sum over all `n`-element subsets `t` of `{3, ..., n+3}` of the
product of the elements of `t`.

A001711 (offset 0) is titled Generalized Stirling numbers `[n+4,4]_3`, i.e. the
`r`-Stirling numbers of the first kind (Broder 1984) with `r = 3`. These are defined by
`[n,k]_r = 0` for `n < r`, `[r,k]_r = 1` if `k = r` and `0` otherwise, and
`[n,k]_r = (n-1) [n-1,k]_r + [n-1,k-1]_r` for `n > r` (with `[n-1,-1]_r = 0`).
Below `rStirling r m k` is `[r+m, k]_r`, so that A001711(n) = `rStirling 3 (n+1) 4`.

The phrase essentially the same is read as: the two sequences agree term by term on the
common range of indices, `A024187(n) = A001711(n)` for every `n >= 1` (A001711 has the
extra initial term `A001711(0) = 1`).
-/

namespace OMA.S_oeis_a024187

/-- `A024187(n)`: the `n`-th elementary symmetric function of `3, 4, ..., n+3`. -/
def a (n : ℕ) : ℕ :=
  ∑ t ∈ (Finset.Icc 3 (n + 3)).powersetCard n, ∏ i ∈ t, i

/-- `rStirling r m k` is the `r`-Stirling number of the first kind `[r+m, k]_r`. -/
def rStirling (r : ℕ) : ℕ → ℕ → ℕ
  | 0, k => if k = r then 1 else 0
  | m + 1, 0 => (r + m) * rStirling r m 0
  | m + 1, k + 1 => (r + m) * rStirling r m (k + 1) + rStirling r m k

/-- `A001711(n) = [n+4, 4]_3`. -/
def A001711 (n : ℕ) : ℕ := rStirling 3 (n + 1) 4

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A001711 n := by
  sorry

end OMA.S_oeis_a024187
