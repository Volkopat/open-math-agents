import Mathlib

/-!
# When is $1 + \frac14 + \frac19 + \cdots + \frac1{n^2}$ the square of a rational?

Source: https://math.stackexchange.com/questions/997604
Credit: @SulkBash

## The problem (as the source states it)

Which $n$ can let $S = 1 + \frac14 + \frac19 + \cdots + \frac1{n^2}$ be a square of a rational
number? Obviously $1$ and $3$ work, but how to prove they are the only ones?

$S$ is the generalized harmonic number $H_n^{(2)}$, whose numerators are the Wolstenholme
numbers (OEIS A007406). The values are $H_1^{(2)} = 1 = 1^2$ and
$H_3^{(2)} = \frac{49}{36} = \left(\frac76\right)^2$. A comment on the source reports a computer
check that no other $n \le 100000$ works. The question is open.

## Formalization notes

* $S$ is `∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2`, as in `OeisA7406.a` upstream.
* "A square of a rational number" is `IsSquare` in `ℚ`, i.e. `S = r * r` for some `r : ℚ`.
* The source's sum starts at $1$, so $n$ ranges over positive integers. We exclude $n = 0$
  explicitly: there the sum is empty, and $0 = 0^2$ would be a degenerate solution.
* The source asks for a proof that $1$ and $3$ are the only solutions. `main` states that the set
  of solutions is exactly $\{1, 3\}$.
-/

namespace OMA.S_mse_997604

/-- The sum $1 + \frac14 + \cdots + \frac1{n^2}$ is the square of a rational number exactly for
$n = 1$ and $n = 3$. -/
theorem main :
    {n : ℕ | 1 ≤ n ∧ IsSquare (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2)} = {1, 3} := by
  sorry

end OMA.S_mse_997604
