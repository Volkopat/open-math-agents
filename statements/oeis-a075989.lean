import Mathlib

/-!
# A075989: Number of k with 1 <= k <= n and {n/k} >= 1/2

Source: https://oeis.org/A075989
Credit: @jagong-cmu

Formalizes Benedict W. J. Irwin's OEIS A075989 conjecture (Sep 22 2016), offset 1:
`Conjecture: Let f(a,b)=1, if (a+b) mod |a-b| != (a mod |a-b|)+(b mod |a-b|), and 0 otherwise.`
`a(n) = Sum_{k=1..n-1} f(n,k).`

The entry also holds a second, analytic conjecture of Benoit Cloitre (Oct 21 2012) on the error
term `a(n) = (2*(log 2)-1)*n + O(n^(1/4 + epsilon))`. That one is of the type of the Dirichlet
divisor problem; this file states only the combinatorial conjecture of Irwin quoted above.

Conventions:
* `a(n)` counts the `k` with `1 <= k <= n` such that the fractional part `{n/k} = n/k - floor(n/k)`
  is at least `1/2`, with `n/k` computed in `ℚ` and `{x}` written `Int.fract x`.
* `f(a,b)` is defined on `ℤ`, with `|a-b|` the absolute value and `mod` the Euclidean remainder `%`
  on `ℤ`. In the sum, `1 <= k <= n-1`, so `|n-k| = n-k > 0` and every remainder is the usual one.
* The claim is stated for every `n >= 1` (the offset is 1). For `n = 1` the sum is empty.
-/

namespace OMA.S_oeis_a075989

/-- `a(n)` = number of `k` with `1 <= k <= n` and `{n/k} >= 1/2`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k : ℕ => (1 : ℚ) / 2 ≤ Int.fract ((n : ℚ) / k))).card

/-- `f(a,b) = 1` if `(a+b) mod |a-b| != (a mod |a-b|) + (b mod |a-b|)`, and `0` otherwise. -/
def f (x y : ℤ) : ℕ :=
  if (x + y) % |x - y| ≠ x % |x - y| + y % |x - y| then 1 else 0

/-- For every `n >= 1`: `a(n) = Sum_{k=1..n-1} f(n,k)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.Ico 1 n, f n k := by
  sorry

end OMA.S_oeis_a075989
