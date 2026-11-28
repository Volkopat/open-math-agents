import Mathlib

/-!
# A294512: Lang's conjecture a(n) = A250400(n+1)/(n+1)

Source: https://oeis.org/A294512
Credit: @avivorly

Entry (Wolfdieter Lang, Nov 01 2017), offset 0: denominators of partial sums of the reciprocals of octagonal numbers.
The octagonal numbers are here A000567(k+1) = (k + 1)*(3*k + 1), k >= 0. The formula section states:
a(n) = denominator(V(3,1;n)) with V(3,1;n) = Sum_{k=0..n} 1/((k + 1)*(3*k + 1)), n >= 0, and
a(n) = A250400(n+1)/(n+1), n >= 0. [conjecture].
Entry A250400 (offset 1): numerator of the harmonic mean of the first n octagonal numbers.

Conventions:
- `a n` is the denominator, in lowest terms, of V(3,1;n). The m-th octagonal number is m*(3*m - 2), and the harmonic
  mean of x_1, ..., x_m is m / (1/x_1 + ... + 1/x_m); `b m` is the numerator, in lowest terms, of that harmonic mean.
- The identity is stated in the rationals, so no integer division is involved.
- Data: a(0..9) = 1, 8, 168, 420, 5460, 14560, 276640, 3043040, 136936800, 136936800 and
  A250400(1..10) = 1, 16, 504, 1680, 27300, 87360, 1936480, 24344320, 1232431200, 1369368000 (the entries' data).
-/

namespace OMA.S_oeis_a294512

/-- V(3,1;n) = Sum_{k=0..n} 1/((k+1)(3k+1)). -/
def V (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / ((k + 1) * (3 * k + 1))

/-- A294512(n), the denominator of V(3,1;n). -/
def a (n : ℕ) : ℕ := (V n).den

/-- A250400(m), the numerator of the harmonic mean of the first m octagonal numbers. -/
def b (m : ℕ) : ℤ :=
  ((m : ℚ) / ∑ k ∈ Finset.Icc 1 m, (1 : ℚ) / ((k : ℚ) * (3 * k - 2))).num

/-- Lang's conjecture: a(n) = A250400(n+1)/(n+1) for every n >= 0. -/
theorem main : ∀ n : ℕ, (a n : ℚ) = (b (n + 1) : ℚ) / ((n : ℚ) + 1) := by
  sorry

end OMA.S_oeis_a294512
