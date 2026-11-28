import Mathlib

/-!
# A306821: denominators of the inverse binomial transform of the swapped original Bernoulli numbers

Source: https://oeis.org/A306821
Credit: @avivorly

A306821 (Paul Curtz, 2019): inverse binomial transform of the original Bernoulli numbers
`[A164555(n)/A027642(n)]` with `1` and `1/2` swapped. Denominators.
The fractions are `1/2, 1/2, -4/3, 2, -38/15, 3, -73/21, 4, -68/15, 5, -179/33, 6, -9218/1365, ...`
(offset 0); their numerators are A307974.

Conjecture (in the entry, %C): `a(2n) same as denominators of cosecant numbers A001897 for n>0
(conjectured).`

A001897 (%N): denominators of cosecant numbers: `-2*(2^(2*n-1)-1)*Bernoulli(2*n)` (offset 0; data
`1, 3, 15, 21, 15, 33, 1365, 3, 255, 399, ...`).

Conventions:
- The original Bernoulli numbers `A164555(k)/A027642(k)` are the Bernoulli numbers with `B_1 = +1/2`,
  which is Mathlib's `bernoulli'` (`1, 1/2, 1/6, 0, -1/30, ...`). Swapping the first two terms gives
  `b 0 = 1/2`, `b 1 = 1` and `b k = bernoulli' k` for `k ≥ 2` (as in the entry's Mathematica
  program, where `BernoulliB[k]` agrees with `bernoulli' k` for `k ≥ 2`).
- The inverse binomial transform is `t n = ∑_{k=0}^{n} (-1)^(n-k) * C(n,k) * b k`, and
  `A306821 n` is the denominator `(t n).den` (a positive natural number).
- `A001897 n` is the denominator (`Rat.den`) of `-2 * (2^(2*n-1) - 1) * B(2*n)` computed in `ℚ`,
  with the exponent `2*n-1` an integer (`zpow`), so that `A001897 0 = 1`; for the even index `2*n`
  Mathlib's `bernoulli` and `bernoulli'` agree.
- Small cases by hand: `t 0 = 1/2`, `t 1 = -1/2 + 1 = 1/2`, `t 2 = 1/2 - 2 + 1/6 = -4/3`,
  `t 3 = -1/2 + 3 - 1/2 + 0 = 2`, `t 4 = 1/2 - 4 + 1 - 0 - 1/30 = -38/15`,
  `t 5 = -1/2 + 5 - 5/3 + 0 + 1/6 - 0 = 3`, `t 6 = 1/2 - 6 + 5/2 - 0 - 1/2 - 0 + 1/42 = -73/21`,
  so `A306821 0..6 = 2, 2, 3, 1, 15, 1, 21` (the data). `A001897 0..3 = den 1, den (-1/3),
  den (7/15), den (-31/21) = 1, 3, 15, 21`. Checks: `A306821 2 = 3`, `A306821 4 = 15`,
  `A306821 6 = 21`.
-/

namespace OMA.S_oeis_a306821

/-- The original Bernoulli numbers (`B_1 = +1/2`, Mathlib's `bernoulli'`) with the first two terms
`1` and `1/2` swapped. -/
def b (k : ℕ) : ℚ := if k = 0 then 1 / 2 else if k = 1 then 1 else bernoulli' k

/-- The inverse binomial transform of `b`. -/
def t (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * b k

/-- A306821: the denominators of `t`. -/
def A306821 (n : ℕ) : ℕ := (t n).den

/-- A001897: denominators of the cosecant numbers `-2*(2^(2*n-1)-1)*Bernoulli(2*n)`. -/
def A001897 (n : ℕ) : ℕ := (-2 * ((2 : ℚ) ^ ((2 * n : ℤ) - 1) - 1) * bernoulli (2 * n)).den

theorem main : ∀ n : ℕ, 0 < n → A306821 (2 * n) = A001897 n := by
  sorry

end OMA.S_oeis_a306821
