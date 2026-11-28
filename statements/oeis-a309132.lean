import Mathlib

/-!
# A309132: a(n) is the denominator of F(n) = A027641(n-1)/n + A027642(n-1)/n^2.

Source: https://oeis.org/A309132
Credit: @divmxnd0x

Conjecture (stated in A309132): for `n > 1`, `a(n) = 1` if and only if `n` is prime.

Formalization notes:
* A027641(m)/A027642(m) is the Bernoulli number `B_m` in lowest terms with `B_1 = -1/2`, i.e.
  Mathlib's `bernoulli m` (its numerator `.num` and denominator `.den`).
* `F(n) = num(B_{n-1})/n + den(B_{n-1})/n^2` in `ℚ` and `a(n)` is its reduced denominator
  (data `1, 1, 1, 16, 1, 36, 1, 64, 27, 100, ...`).
-/

namespace OMA.S_oeis_a309132

/-- `F(n) = num(B_{n-1})/n + den(B_{n-1})/n^2`. -/
def F (n : ℕ) : ℚ := ((bernoulli (n - 1)).num : ℚ) / n + ((bernoulli (n - 1)).den : ℚ) / n ^ 2

/-- A309132(n): the denominator of `F(n)`. -/
def a (n : ℕ) : ℕ := (F n).den

/-- For `n > 1`, `a(n) = 1` iff `n` is prime. -/
theorem main : ∀ n : ℕ, 1 < n → (a n = 1 ↔ n.Prime) := by
  sorry

end OMA.S_oeis_a309132
