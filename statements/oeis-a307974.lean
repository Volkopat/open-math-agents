import Mathlib

/-!
# A307974: numerators of the inverse binomial transform of the swapped original Bernoulli numbers

Source: https://oeis.org/A307974
Credit: @avivorly

A307974 (Paul Curtz, 2019): inverse binomial transform of the original Bernoulli numbers
`[A164555(n)/A027642(n)]` with `1` and `1/2` swapped. Numerators.
The fractions are `1/2, 1/2, -4/3, 2, -38/15, 3, -73/21, 4, ...` (offset 0).

Conjectures (in the entry):
- %F: `a(2*n+1) = n+1 (conjectured).`
- %C: `Denominators 3, 15, 21, 15, 33, 1365, 3, 255, ... coincide with cosecant numbers A001897,
  except 1 (conjectured).`

A001897 (%N): denominators of cosecant numbers: `-2*(2^(2*n-1)-1)*Bernoulli(2*n)` (offset 0; data
`1, 3, 15, 21, 15, 33, 1365, 3, 255, 399, ...`).

Conventions:
- The original Bernoulli numbers `A164555(k)/A027642(k)` are the Bernoulli numbers with `B_1 = +1/2`,
  which is Mathlib's `bernoulli'` (`1, 1/2, 1/6, 0, -1/30, ...`). Swapping the first two terms gives
  `b 0 = 1/2`, `b 1 = 1` and `b k = bernoulli' k` for `k ≥ 2` (as in the entry's Mathematica
  program, where `BernoulliB[k]` agrees with `bernoulli' k` for `k ≥ 2`).
- The inverse binomial transform is `t n = ∑_{k=0}^{n} (-1)^(n-k) * C(n,k) * b k`, and
  `A307974 n` is the numerator `(t n).num` (an integer, carrying the sign).
- `A001897 n` is the denominator (`Rat.den`) of `-2 * (2^(2*n-1) - 1) * B(2*n)` computed in `ℚ`,
  with the exponent `2*n-1` an integer (`zpow`), so that `A001897 0 = 1`; for the even index `2*n`
  Mathlib's `bernoulli` and `bernoulli'` agree.
- The %C conjecture is read as: for every `n ≥ 1`, the denominator of `t (2*n)` equals
  `A001897 n` (the listed denominators `3, 15, 21, ...` are those of `t 2, t 4, t 6, ...`; the
  excepted `1` is `A001897 0` and the odd-index denominators `1`).
- Small cases by hand: `t 0 = 1/2`, `t 1 = -1/2 + 1 = 1/2`, `t 2 = 1/2 - 2 + 1/6 = -4/3`,
  `t 3 = -1/2 + 3 - 1/2 + 0 = 2`, `t 4 = 1/2 - 4 + 1 - 0 - 1/30 = -38/15`,
  `t 5 = -1/2 + 5 - 5/3 + 0 + 1/6 - 0 = 3`, `t 6 = 1/2 - 6 + 5/2 - 0 - 1/2 - 0 + 1/42 = -73/21`,
  so `A307974 0..6 = 1, 1, -4, 2, -38, 3, -73` (the data). `A001897 0..3 = den 1, den (-1/3),
  den (7/15), den (-31/21) = 1, 3, 15, 21`. Checks: `A307974 1 = 1`, `A307974 3 = 2`,
  `A307974 5 = 3`; `den (t 2) = 3`, `den (t 4) = 15`, `den (t 6) = 21`.
-/

namespace OMA.S_oeis_a307974

/-- The original Bernoulli numbers (`B_1 = +1/2`, Mathlib's `bernoulli'`) with the first two terms
`1` and `1/2` swapped. -/
def b (k : ℕ) : ℚ := if k = 0 then 1 / 2 else if k = 1 then 1 else bernoulli' k

/-- The inverse binomial transform of `b`. -/
def t (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * b k

/-- A307974: the numerators of `t`. -/
def A307974 (n : ℕ) : ℤ := (t n).num

/-- A001897: denominators of the cosecant numbers `-2*(2^(2*n-1)-1)*Bernoulli(2*n)`. -/
def A001897 (n : ℕ) : ℕ := (-2 * ((2 : ℚ) ^ ((2 * n : ℤ) - 1) - 1) * bernoulli (2 * n)).den

theorem main :
    (∀ n : ℕ, A307974 (2 * n + 1) = n + 1) ∧
      (∀ n : ℕ, 1 ≤ n → (t (2 * n)).den = A001897 n) := by
  sorry

end OMA.S_oeis_a307974
