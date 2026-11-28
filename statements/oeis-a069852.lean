import Mathlib

/-!
# OEIS A069852: `a(n) = Σ_{i=0..2n} B(i) C(2n+1, i) 5^i`

Source: https://oeis.org/A069852
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n) = Sum_{i=0..2n} B(i)*C(2n+1,i)*5^i`, where `B(i)` are the Bernoulli numbers and `C` the
binomial coefficients, offset 1 (`6, -74, 1946, -88434, 6154786, …`).

The entry (Peter Bala, Mar 02 2015) gives `a(n) = 5^(2n+1) * B(2n+1, 1/5)`, where `B(n, x)` is the
n-th Bernoulli polynomial, and adds: "Conjecturally, a(n) = the signed numerator of
B(2*n + 1,1/5)." This file states that conjecture.

Conventions:
* `B(i)` is Mathlib's `bernoulli i`, with `B(1) = -1/2`. This is the convention of the entry: with
  it the defining sum gives `a(1) = 1 - 15/2 + 25/2 = 6`, as in the data, while `B(1) = +1/2`
  would give `21`.
* `B(m, x)` is Mathlib's `Polynomial.bernoulli m` evaluated at `x`.
* "Signed numerator" is the numerator of the rational number in lowest terms, with its sign
  (`Rat.num`); for example `B(3, 1/5) = 6/125` and `B(5, 1/5) = -74/3125`.
* The statement is for every `n ≥ 1`, the offset of the entry.
* A computation with exact rationals confirms that this definition reproduces the data of the
  entry and that the conjectured identity holds for `1 ≤ n ≤ 30`.
-/

namespace OMA.S_oeis_a069852

/-- `A069852(n) = Σ_{i=0..2n} B(i) C(2n+1, i) 5^i`. -/
noncomputable def a (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (2 * n + 1), bernoulli i * ((2 * n + 1).choose i : ℚ) * 5 ^ i

/-- Conjecture (Bala): for `n ≥ 1`, `a(n)` is the signed numerator of `B(2n+1, 1/5)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = (((Polynomial.bernoulli (2 * n + 1)).eval (1 / 5 : ℚ)).num : ℚ) := by
  sorry

end OMA.S_oeis_a069852
