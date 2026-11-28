import Mathlib

/-!
# A036968: Genocchi numbers (of first kind): expansion of 2*x/(exp(x)+1).

Source: https://oeis.org/A036968
Credit: @divmxnd0x

Conjecture (stated in A036968): for any positive integer `n`, `-a(n+1)` is the permanent of the
`n × n` matrix `M` with `M(j, k) = floor((2j - k)/n)` (`j, k = 1..n`).

Formalization notes:
* `a n` is the `n`-th Genocchi number of the first kind, the coefficient of `x^n / n!` in
  `2x / (exp(x) + 1)`; it equals `2 (1 - 2^n) B_n` with Mathlib's Bernoulli numbers `bernoulli n`
  (convention `B_1 = -1/2`), giving `a 0, a 1, ... = 0, 1, -1, 0, 1, 0, -3, 0, 17, ...`.
* The matrix is indexed by `Fin n`, the entry at `(j, k)` being `floor((2(j+1) - (k+1)) / n)`;
  integer division `/` on `ℤ` by the positive `n` is floor division.
-/

namespace OMA.S_oeis_a036968

/-- A036968(n): the Genocchi number of the first kind, `2 (1 - 2^n) B_n`. -/
def a (n : ℕ) : ℚ := 2 * (1 - 2 ^ n) * bernoulli n

/-- The `n × n` matrix `M(j, k) = floor((2j - k)/n)`, `j, k = 1..n`. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun j k => (2 * ((j : ℤ) + 1) - ((k : ℤ) + 1)) / (n : ℤ)

/-- For every `n ≥ 1`, `-a(n+1)` is the permanent of `M n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → -a (n + 1) = ((M n).permanent : ℚ) := by
  sorry

end OMA.S_oeis_a036968
