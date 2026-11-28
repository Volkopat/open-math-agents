import Mathlib

/-!
# A370691: Scheuerle's conjecture T(n, 2) = A128507(n)

Source: https://oeis.org/A370691
Credit: @avivorly

Entry A370691 (Thomas Scheuerle, Apr 21 2024), offset 0: square array read by upward antidiagonals,
T(n, k) = denominator( 2*k!*(-2)^k*Sum_{m=1..n}( 1/(2*m-1)^(k+1) ) ).
Its formula section states: "Conjectured: T(n, 2) = A128507(n)."

Entry A128507 (Wolfdieter Lang, Apr 04 2007), offset 0: denominators of partial sums for a series for
3*sqrt(2)*(Pi^3)/2^7; a(n) = denominator(r(n)) with the rationals r(n) = Sum_{k=0..n} S(2*k,sqrt(2))/(2*k+1)^3 with
Chebyshev's S-Polynomials S(2*k,sqrt(2))=[1,1,-1,-1] periodic sequence with period 4.

Conventions:
- `T n k` is the denominator, in lowest terms, of the rational number 2*k!*(-2)^k*Sum_{m=1..n} 1/(2*m-1)^(k+1),
  computed in `ℚ` (so `2*m - 1` is exact); for `n = 0` the sum is empty, the value is `0` and `T 0 k = 1`.
- `S` is Mathlib's `Polynomial.Chebyshev.S` (`S(0,x) = 1`, `S(1,x) = x`, `S(j+2,x) = x*S(j+1,x) - S(j,x)`),
  evaluated at `x = √2` in `ℝ`, and `r n` is the real sum of the formula. `A128507 n` is the denominator of the
  rational number whose real value is `r n` (a rational number is determined by its real value; `r n` is rational
  because `S(2*k, √2) ∈ {1, -1}`, so the fallback value `0` is never used).
- Offsets. Both entries have offset 0. The `%e` table of A370691 has column `k = 2` equal to
  1, 1, 27, 3375, 1157625, 31255875, 41601569625 for n = 0..6, while A128507 begins
  1, 27, 3375, 1157625, 31255875, 41601569625. So the literal reading `T(n, 2) = A128507(n)` already differs at
  `n = 1` (`T(1, 2) = 1`, `A128507(1) = 27`), and the data fit the shifted reading `T(n + 1, 2) = A128507(n)`.
  `main` states the conjecture as the disjunction of the two readings, so a disproof refutes both.
-/

namespace OMA.S_oeis_a370691

/-- A370691: `T(n, k) = denominator(2 * k! * (-2)^k * Sum_{m=1..n} 1/(2m-1)^(k+1))`. -/
def T (n k : ℕ) : ℕ :=
  (2 * (k.factorial : ℚ) * (-2) ^ k * ∑ m ∈ Finset.Icc 1 n, 1 / (2 * (m : ℚ) - 1) ^ (k + 1)).den

/-- The partial sum `r(n) = Sum_{k=0..n} S(2k, √2)/(2k+1)^3` of A128507, with Chebyshev's `S`-polynomials. -/
noncomputable def r (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Polynomial.Chebyshev.S ℝ (2 * (k : ℤ))).eval (Real.sqrt 2) / (2 * (k : ℝ) + 1) ^ 3

open Classical in
/-- A128507(n): the denominator of the rational number `r(n)`. -/
noncomputable def A128507 (n : ℕ) : ℕ :=
  if h : ∃ q : ℚ, (q : ℝ) = r n then h.choose.den else 0

/-- Scheuerle's conjecture `T(n, 2) = A128507(n)`, under the literal offset or the shifted one. -/
theorem main : (∀ n : ℕ, T n 2 = A128507 n) ∨ (∀ n : ℕ, T (n + 1) 2 = A128507 n) := by
  sorry

end OMA.S_oeis_a370691
